(*****************************************************************************

  Liquidsoap, a programmable stream generator.
  Copyright 2003-2026 Savonet team

  This program is free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details, fully stated in the COPYING
  file at the root of the liquidsoap distribution.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301  USA

 *****************************************************************************)

(* A true-peak limiter.

   A sample-peak limiter cannot see the peak that the decoder of a lossy codec
   rebuilds between two samples. A 0 dBFS sample peak easily decodes 0.5 to 1 dB
   above 0 dBFS after MP3 or AAC encoding, which clips. This operator detects the
   peak of the signal reconstructed between the samples and holds the gain low
   long enough for the decoder not to overshoot.

   Detection runs on a polyphase, Kaiser-windowed sinc interpolator. The gain has
   an instantaneous attack and a release, and the applied gain is the minimum of
   the last [lookahead] gains, so the reduction is already in place when the peak
   reaches the output.

   The interpolation filter is causal and delayed by [taps / 2] samples, which is
   why a lookahead shorter than that cannot guarantee the ceiling. *)

open Mm
open Source

(* Modified Bessel function of the first kind, order 0: the Kaiser window. *)
let bessel_i0 x =
  let q = x *. x /. 4. in
  let rec loop k term acc =
    if k > 60 then acc
    else
      let term = term *. q /. (float_of_int (k + 1) *. float_of_int (k + 1)) in
      if term < 1e-14 *. acc then acc else loop (k + 1) term (acc +. term)
  in
  loop 0 1. 1.

(* [coef.(p).(j)] weights the input sample [j] samples ago to reconstruct the
   sub-sample at offset [p / factor] of a sample. Each phase has a unit DC gain:
   the truncation of the sinc is compensated, otherwise quiet signals would be
   attenuated and loud ones overestimated. *)
let design ~factor ~taps ~beta =
  let half = float_of_int taps /. 2. in
  let i0_beta = bessel_i0 beta in
  Array.init factor (fun phase ->
      let phase = float_of_int phase /. float_of_int factor in
      let row =
        Array.init taps (fun j ->
            let u = float_of_int j -. half +. phase in
            let sinc =
              if u = 0. then 1. else sin (Float.pi *. u) /. (Float.pi *. u)
            in
            let window =
              if abs_float u >= half then 0.
              else
                let r = u /. half in
                bessel_i0 (beta *. sqrt (max 0. (1. -. (r *. r)))) /. i0_beta
            in
            sinc *. window)
      in
      let total = Array.fold_left ( +. ) 0. row in
      if total = 0. then row else Array.map (fun v -> v /. total) row)

(* Minimum of the last [window] gain values in amortized constant time. *)
module Sliding_min = struct
  type t = {
    index : int array;
    value : float array;
    cap : int;
    mutable head : int;
    mutable tail : int;
    mutable len : int;
  }

  let make cap =
    {
      index = Array.make cap 0;
      value = Array.make cap 0.;
      cap;
      head = 0;
      tail = 0;
      len = 0;
    }

  let clear t =
    t.head <- 0;
    t.tail <- 0;
    t.len <- 0

  let min t = if t.len = 0 then 1. else t.value.(t.head)

  let push t index v =
    while t.len > 0 && t.value.((t.tail - 1 + t.cap) mod t.cap) >= v do
      t.tail <- (t.tail - 1 + t.cap) mod t.cap;
      t.len <- t.len - 1
    done;
    t.index.(t.tail) <- index;
    t.value.(t.tail) <- v;
    t.tail <- (t.tail + 1) mod t.cap;
    t.len <- t.len + 1

  let expire t oldest =
    while t.len > 0 && t.index.(t.head) < oldest do
      t.head <- (t.head + 1) mod t.cap;
      t.len <- t.len - 1
    done
end

let taps = 24
let beta = 8.

class true_peak_limit ~threshold ~release ~pre_gain ~lookahead ~factor
  ~track_sensitive ~field (source : source) =
  let samplerate = float (Lazy.force Frame.audio_rate) in
  (* The delay, in samples. Zero or one sample of lookahead still works but only
     the detection delay of the interpolator is available to reduce the gain. *)
  let delay_len = max 1 (int_of_float (lookahead *. samplerate +. 0.5)) in
  let coef = design ~factor ~taps ~beta in
  object (self)
    inherit operator ~name:"true_peak_limit" [source]
    method fallible = source#fallible
    method remaining = source#remaining
    method effective_source = source#effective_source
    method self_sync = source#self_sync
    method private can_generate_frame = source#is_ready
    method abort_track = source#abort_track

    (* Gain and detected peak, both useful for monitoring. *)
    val mutable gain = 1.
    method gain = gain

    val mutable peak = 0.
    method peak = peak

    (* Ring buffer of the last [taps] input samples, shared by all channels. *)
    val mutable history = [||]
    val mutable history_pos = 0

    (* Delay line: what goes out now went in [delay_len] samples ago. *)
    val mutable line = [||]
    val mutable line_pos = 0

    (* Absolute index of the sample being processed, and the sliding minimum. *)
    val mutable index = 0
    val mutable min_gain = Sliding_min.make (delay_len + 4)

    method private prepare channels =
      if Array.length line <> channels || Audio.Mono.length line.(0) <> delay_len
      then (
        line <- Array.init channels (fun _ -> Array.make delay_len 0.);
        line_pos <- 0;
        if Array.length history <> channels then (
          history <- Array.init channels (fun _ -> Array.make taps 0.);
          history_pos <- 0))

    method private reset =
      gain <- 1.;
      Sliding_min.clear min_gain

    method private limit frame =
      let pos = AFrame.position frame in
      let buf = Content.Audio.get_data (Frame.get frame field) in
      let channels = Array.length buf in
      self#prepare channels;
      let threshold = threshold () in
      let tlin = Audio.lin_of_dB threshold in
      let release = release () in
      let pre_gain = pre_gain () in
      let pg = Audio.lin_of_dB pre_gain in
      let release_coef =
        1. -. exp (-1. /. (max 1e-4 release *. samplerate))
      in
      for i = 0 to pos - 1 do
        (* New sample of every channel goes to the interpolator history. *)
        for c = 0 to channels - 1 do
          history.(c).(history_pos) <- buf.(c).(i) *. pg
        done;
        (* Peak of the signal reconstructed between samples. *)
        let p = ref 0. in
        for c = 0 to channels - 1 do
          let h = history.(c) in
          let raw = abs_float h.(history_pos) in
          if raw > !p then p := raw;
          for phase = 0 to factor - 1 do
            let row = coef.(phase) in
            let acc = ref 0. in
            for j = 0 to taps - 1 do
              let idx = (history_pos - j + taps) mod taps in
              acc := !acc +. row.(j) *. h.(idx)
            done;
            let a = abs_float !acc in
            if a > !p then p := a
          done
        done;
        (* Never let a damaged sample poison the gain. *)
        let p = if Float.is_nan !p || !p = infinity then 0. else !p in
        peak <- p;
        history_pos <- (history_pos + 1) mod taps;
        (* A threshold above 0 dBTP must not turn the limiter into a booster. *)
        let target = if p <= tlin then 1. else Float.min 1. (tlin /. p) in
        if target < gain then gain <- target
        else gain <- gain +. (release_coef *. (target -. gain));
        Sliding_min.push min_gain index gain;
        Sliding_min.expire min_gain (index - delay_len);
        let g = Sliding_min.min min_gain in
        for c = 0 to channels - 1 do
          let out = line.(c).(line_pos) in
          line.(c).(line_pos) <- buf.(c).(i) *. pg;
          buf.(c).(i) <- out *. g
        done;
        line_pos <- (line_pos + 1) mod delay_len;
        index <- index + 1
      done;
      Frame.set_data frame field Content.Audio.lift_data buf

    method private generate_frame =
      match self#split_frame (source#get_mutable_frame field) with
        | frame, None -> self#limit frame
        | frame, Some new_track ->
            let frame = self#limit frame in
            if track_sensitive then self#reset;
            Frame.append frame (self#limit new_track)
  end

let _ =
  let return_t = Format_type.audio () in
  Lang.add_track_operator ~base:Modules.track_audio "true_peak_limit"
    [
      ( "threshold",
        Lang.getter_t Lang.float_t,
        Some (Lang.float (-1.)),
        Some "Ceiling of the reconstructed peak, in dBTP." );
      ( "lookahead",
        Lang.float_t,
        Some (Lang.float 5.),
        Some
          "Delay used to reduce the gain before a peak reaches the output, in \
           milliseconds. Fixed at start: a value below a millisecond does not \
           leave the interpolator time to react." );
      ( "release",
        Lang.getter_t Lang.float_t,
        Some (Lang.float 80.),
        Some "Release time of the gain, in milliseconds." );
      ( "pre_gain",
        Lang.getter_t Lang.float_t,
        Some (Lang.float 0.),
        Some "Gain applied before detection, in dB." );
      ( "oversample",
        Lang.int_t,
        Some (Lang.int 4),
        Some
          "Oversampling factor of the true-peak detector: 2, 4 or 8. Higher is \
           more accurate and costs more CPU." );
      ( "track_sensitive",
        Lang.bool_t,
        Some (Lang.bool false),
        Some "Reset the gain on every track." );
      ("", return_t, None, None);
    ]
    ~return_t ~category:`Audio
    ~descr:
      "Limit the peak that a decoder reconstructs between samples, so that \
       lossy codecs do not clip. The applied gain is the minimum of the last \
       `lookahead` gains, with an instantaneous attack and the given release."
    ~meth:
      [
        {
          name = "gain";
          scheme = ([], Lang.fun_t [] Lang.float_t);
          descr = "Current gain (dB).";
          value =
            (fun s ->
              Lang.val_fun [] (fun _ -> Lang.float (Audio.dB_of_lin s#gain)));
        };
        {
          name = "peak";
          scheme = ([], Lang.fun_t [] Lang.float_t);
          descr = "Last detected true peak (dBTP).";
          value = (fun s -> Lang.val_fun [] (fun _ -> Lang.float s#peak));
        };
      ]
    (fun p ->
      let pos = Lang.pos p in
      let threshold = List.assoc "threshold" p |> Lang.to_float_getter in
      let release = List.assoc "release" p |> Lang.to_float_getter in
      let release () = release () /. 1000. in
      let pre_gain = List.assoc "pre_gain" p |> Lang.to_float_getter in
      let lookahead = List.assoc "lookahead" p |> Lang.to_float in
      if lookahead < 1. then
        Runtime_error.raise ~pos
          ~message:
            "`lookahead` must be at least 1 ms: the interpolator needs that              time to detect a peak before it reaches the output."
          "eval";
      let lookahead = lookahead /. 1000. in
      let track_sensitive = List.assoc "track_sensitive" p |> Lang.to_bool in
      let factor = List.assoc "oversample" p |> Lang.to_int in
      if factor < 2 || factor > 8 then
        Runtime_error.raise ~pos
          ~message:"`oversample` must be between 2 and 8." "eval";
      let field, s = List.assoc "" p |> Track.of_value in
      ( field,
        new true_peak_limit ~threshold ~release ~pre_gain ~lookahead ~factor
          ~track_sensitive ~field s ))
