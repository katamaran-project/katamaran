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
     NArith.NArith.

(* The target platform: the memory map of the machine the GVT examples run on.

   The ISA layer (Base.v and everything built on it) only refers to the
   symbols below, never to concrete addresses. Kernel code and proofs do the
   same, so the verification does not depend on where things are, only on the
   order and alignment constraints stated alongside. Choosing the physical
   values instead would not change any proof, only make them slower: the
   model enumerates its address space.

   The map follows QEMU's riscv32 `virt` board: all devices sit below RAM, in
   the same order as on the board, but compressed. The physical address of
   each symbol is given in its comment.

   Alignment. The kernel loads some addresses with a single `lui`, either
   directly (low 12 bits zero: 4 KiB aligned) or as a pmpaddr value, i.e.
   shifted right by two (16 KiB aligned). Layouts built on this map state
   those obligations next to the code that needs them. *)

Module Target.
  Local Open Scope N_scope.

  (* ---------------------------------------------------------------------- *)
  (* MMIO window: one contiguous range that holds all devices.              *)
  (* ---------------------------------------------------------------------- *)
  Definition mmio_start : N := 0x0.

  (* 0x00000000 .. 0x02000000: test finisher, RTC, ... (nothing the kernel
     uses; accessible to S-mode) *)

  (* CLINT, 0x02000000 .. 0x02010000 *)
  Definition clint_base      : N := 0x4000.                (* 0x02000000 *)
  Definition clint_size      : N := 0x4000.                (* 0x00010000 *)
  Definition clint_end       : N := clint_base + clint_size.
  Definition clint_mtimecmp0 : N := clint_base + 0x1000.   (* 0x02004000 *)

  (* PLIC, 0x0c000000 .. *)
  Definition plic_base       : N := 0x8000.                (* 0x0c000000 *)
  (* priority of source [irq]: plic_base + 4 * irq *)
  Definition plic_priority (irq : N) : N := plic_base + 4 * irq.
  Definition plic_enable0    : N := plic_base + 0x2000.    (* 0x0c002000, context 0 (M) *)
  Definition plic_enable1    : N := plic_enable0 + 0x80.   (* 0x0c002080, context 1 (S) *)
  Definition plic_threshold0 : N := 0xc000.                (* 0x0c200000, context 0 (M) *)
  Definition plic_claim0     : N := plic_threshold0 + 4.   (* 0x0c200004 *)
  Definition plic_threshold1 : N := plic_threshold0 + 0x1000. (* 0x0c201000, context 1 (S) *)

  (* 0x0c201000 .. 0x10001000: PLIC context 1, UART (accessible to S-mode) *)

  (* virtio-mmio slots, 0x10001000 .. 0x10009000. Only the slot of the button
     device is modelled. *)
  Definition virtio_slots_start : N := 0xe000.             (* 0x10001000 *)
  Definition virtio_base        : N := 0xe000.             (* 0x10008000 *)
  (* IRQ of the button device at the PLIC *)
  Definition virtio_irq         : N := 8.

  (* Memory the button device writes by DMA. On the board this is ordinary
     kernel RAM that the device is told about (the virtqueue and its receive
     buffer). The model has no DMA, so it treats this memory as part of the
     device: the kernel's reads there are MMIO reads, which may return
     anything. *)
  Definition dma_virtq  : N := 0x10000.  (* virtq_mem 0x80031000: two pages, used ring at +0x1000 *)
  Definition dma_rx_buf : N := 0x12000.  (* rx_buf    0x80033000 *)

  (* The device the IO protocol is about (see Sig.v): the LED word, the
     interrupt word at +4, and the shutdown word, which Base.v puts in the
     last word of the MMIO window. Accesses below proto_start are not
     constrained by the protocol.
     On the board the LED is simulated by a PMP-guarded word in kernel RAM
     (KERNEL_RAM_LED_SIM, 0x80030004). The model needs an MMIO address for
     it, because that is where IO events are recorded. *)
  Definition proto_start : N := 0x13000.
  Definition proto_led   : N := proto_start.

  Definition mmio_size : N := 0x14000.
  Definition mmio_end  : N := mmio_start + mmio_size.

  (* ---------------------------------------------------------------------- *)
  (* RAM, 0x80000000 .. 0x88000000                                          *)
  (* ---------------------------------------------------------------------- *)
  Definition ram_start : N := mmio_end.                    (* 0x80000000 *)
  Definition ram_size  : N := 2^16.
  Definition ram_end   : N := ram_start + ram_size.        (* 0x88000000 *)

  (* The map is ordered as on the board and nothing overlaps. *)
  Goal mmio_start <= clint_base /\ clint_end <= plic_base
       /\ plic_enable1 <= plic_threshold0 /\ plic_threshold1 <= virtio_slots_start
       /\ virtio_slots_start <= virtio_base /\ virtio_base + 0x1000 <= dma_virtq
       /\ dma_virtq + 0x2000 <= dma_rx_buf /\ dma_rx_buf + 0x1000 <= proto_start
       /\ proto_start < mmio_end /\ mmio_end <= ram_start.
  Proof. repeat split; now vm_compute. Qed.

  (* The layout inherited from the RiscvPmp case study, which
     StopButtonUMode.v was written against: RAM at 0 (16 KiB), followed by the
     MMIO window, with the protocol device at its start.
       ram_start = 0, ram_size = 2^14,
       mmio_start = ram_end, mmio_size = ram_end + ram_size. *)
End Target.
