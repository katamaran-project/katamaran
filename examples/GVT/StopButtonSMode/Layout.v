(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel, Dominique Devriese, Sander Huyghebaert  *)
(* All rights reserved.                                                       *)
(*                                                                            *)
(* Redistribution and use in source and binary forms, with or without         *)
(* modification, are permitted provided that the following conditions are     *)
(* met:                                                                       *)
(*                                                                            *)
(* 1. Redistributions of source code must retain the above copyright notice,  *)
(*    this list of conditions and the following disclaimer.                   *)
(*                                                                            *)
(* 2. Redistributions in binary form must reproduce the above copyright       *)
(*    notice, this list of conditions and the following disclaimer in the     *)
(*    documentation and/or other materials provided with the distribution.    *)
(*                                                                            *)
(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS        *)
(* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED  *)
(* TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR *)
(* PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR          *)
(* CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,      *)
(* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,        *)
(* PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR         *)
(* PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF     *)
(* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING       *)
(* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS         *)
(* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.               *)
(******************************************************************************)

From Stdlib Require Import
     NArith.NArith
     Lists.List.
From Katamaran Require Import
     RiscvPmp.GVT.Target.

Import ListNotations.

(* The "linker script" of the S-mode StopButton femtokernel: where its code,
   its data and the S-mode payload live on the target, and the PMP regions
   that follow from that. Kernel.v and the proofs only use these symbols.

   The values in the comments are those of the QEMU build (linker script and
   init.S). *)

Module Layout.
  Local Open Scope N_scope.

  (* ---------------------------------------------------------------------- *)
  (* RAM                                                                    *)
  (* ---------------------------------------------------------------------- *)
  Definition code_start          : N := Target.ram_start.            (* KERNEL_ROM_START     0x80000000 *)
  Definition adv_start           : N := Target.ram_start + 0x4000.   (* ADVERSARY_ROM_START  0x80010000 *)
  Definition kernel_ram_start    : N := Target.ram_start + 0x8000.   (* KERNEL_RAM_START     0x80030000 *)
  Definition adversary_ram_start : N := Target.ram_start + 0xc000.   (* ADVERSARY_RAM_START  0x80040000 *)
  Definition ram_end             : N := Target.ram_end.              (* RAM_END              0x88000000 *)

  (* Kernel data *)
  Definition iostate          : N := kernel_ram_start.               (* KERNEL_RAM_IOSTATE   0x80030000 *)
  Definition rx_used_seen     : N := kernel_ram_start + 8.           (* rx_used_seen         0x80033004 *)
  Definition kernel_stack_top : N := adversary_ram_start.            (* __kernel_stack_top   0x80040000 *)

  (* ---------------------------------------------------------------------- *)
  (* Symbols that are kernel RAM on the board but device memory in the      *)
  (* model (see Target.v)                                                   *)
  (* ---------------------------------------------------------------------- *)
  Definition led_sim   : N := Target.proto_led.                      (* KERNEL_RAM_LED_SIM   0x80030004 *)
  Definition virtq_mem : N := Target.dma_virtq.                      (* virtq_mem            0x80031000 *)
  Definition rx_buf    : N := Target.dma_rx_buf.                     (* rx_buf               0x80033000 *)

  (* ---------------------------------------------------------------------- *)
  (* PMP regions, as in init.S: pmpaddr values (address >> 2), all TOR.     *)
  (* Deny-list for S-mode: even entries RWX, odd entries R-X.               *)
  (*   0 [0,                   CLINT)               RWX                     *)
  (*   1 [CLINT,               CLINT end)           R-X  mtimecmp, msip     *)
  (*   2 [..,                  PLIC prio[button])   RWX                     *)
  (*   3 [PLIC prio[button],   +4)                  R-X                     *)
  (*   4 [..,                  PLIC enable0)        RWX                     *)
  (*   5 [PLIC enable0,        PLIC enable1)        R-X  M context          *)
  (*   6 [..,                  PLIC threshold0)     RWX                     *)
  (*   7 [PLIC threshold0,     PLIC threshold1)     R-X  M context          *)
  (*   8 [..,                  virtio slots)        RWX  PLIC S context     *)
  (*   9 [virtio slots,        adv_start)           R-X  virtio, device     *)
  (*                                                     memory, kernel code*)
  (*  10 [adv_start,           kernel_ram_start)    RWX  S-mode image       *)
  (*  11 [kernel_ram_start,    adversary_ram_start) R-X  kernel RAM         *)
  (*  12 [adversary_ram_start, ram_end)             RWX  S-mode RAM         *)
  (* ---------------------------------------------------------------------- *)
  Definition pmpaddr (a : N) : N := a / 4.

  Definition region0  : N := pmpaddr Target.clint_base.                            (* 0x00800000 *)
  Definition region1  : N := pmpaddr Target.clint_end.                             (* 0x00804000 *)
  Definition region2  : N := pmpaddr (Target.plic_priority Target.virtio_irq).     (* 0x03000008 *)
  Definition region3  : N := pmpaddr (Target.plic_priority (Target.virtio_irq + 1)). (* 0x03000009 *)
  Definition region4  : N := pmpaddr Target.plic_enable0.                          (* 0x03000800 *)
  Definition region5  : N := pmpaddr Target.plic_enable1.                          (* 0x03000820 *)
  Definition region6  : N := pmpaddr Target.plic_threshold0.                       (* 0x03080000 *)
  Definition region7  : N := pmpaddr Target.plic_threshold1.                       (* 0x03080400 *)
  Definition region8  : N := pmpaddr Target.virtio_slots_start.                    (* 0x04000400 *)
  Definition region9  : N := pmpaddr adv_start.                                    (* 0x20004000 *)
  Definition region10 : N := pmpaddr kernel_ram_start.                             (* 0x2000c000 *)
  Definition region11 : N := pmpaddr adversary_ram_start.                          (* 0x20010000 *)
  Definition region12 : N := pmpaddr ram_end.                                      (* 0x22000000 *)

  Definition regions : list N :=
    [region0; region1; region2; region3; region4; region5; region6;
     region7; region8; region9; region10; region11; region12].

  (* ---------------------------------------------------------------------- *)
  (* Obligations                                                            *)
  (* ---------------------------------------------------------------------- *)

  (* TOR needs ascending bounds (the .if/.error checks in init.S). *)
  Goal region0 <= region1 /\ region1 <= region2 /\ region2 <= region3 /\ region3 <= region4
       /\ region4 <= region5 /\ region5 <= region6 /\ region6 <= region7 /\ region7 <= region8
       /\ region8 <= region9 /\ region9 <= region10 /\ region10 <= region11 /\ region11 <= region12.
  Proof. repeat split; now vm_compute. Qed.

  (* The region bounds are word aligned, so `>> 2` loses nothing. *)
  Goal map (fun r => 4 * r) regions =
       [Target.clint_base; Target.clint_end;
        Target.plic_priority Target.virtio_irq; Target.plic_priority (Target.virtio_irq + 1);
        Target.plic_enable0; Target.plic_enable1;
        Target.plic_threshold0; Target.plic_threshold1;
        Target.virtio_slots_start; adv_start; kernel_ram_start; adversary_ram_start; ram_end].
  Proof. now vm_compute. Qed.

  (* The layout fits the target, in the order the PMP regions rely on. *)
  Goal code_start < adv_start /\ adv_start < kernel_ram_start
       /\ kernel_ram_start < adversary_ram_start /\ adversary_ram_start < ram_end
       /\ rx_used_seen + 4 <= kernel_stack_top
       /\ Target.virtio_slots_start <= Target.virtio_base
       /\ Target.proto_start + 0x1000 <= code_start.
  Proof. repeat split; now vm_compute. Qed.
End Layout.
