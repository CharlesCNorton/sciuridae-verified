(******************************************************************************)
(*  Conservation.v                                                            *)
(*                                                                            *)
(*  IUCN Red List categories as recorded by MDD v2.5.  "NE" (not evaluated)   *)
(*  mostly marks species recognised after the last assessment; MDD notes when *)
(*  a status was assessed under an older name.                                *)
(******************************************************************************)

From Coq Require Import List Bool Arith Lia String.
From Sciuridae Require Import Lib.Base Data.Geography Data.Taxonomy Data.Species Classification.
Import ListNotations.

Definition threatened (c : IUCN) : bool :=
  match c with VU | EN | CR => true | _ => false end.

Theorem iucn_tally :
  map (fun c => (c, count (fun s => beq (iucn (info s)) c) enum)) enum =
  [(LC, 195); (NT, 22); (VU, 14); (EN, 14); (CR, 4); (EW, 0); (EX, 0); (DD, 28); (NE, 44)].
Proof. vm_compute. reflexivity. Qed.

Theorem threatened_count : count (fun s => threatened (iucn (info s))) enum = 32.
Proof. vm_compute. reflexivity. Qed.

Theorem critically_endangered :
  filter (fun s => beq (iucn (info s)) CR) enum =
  [sp Callosciurus_honkhoaiensis; sp Biswamoyopterus_biswasi;
   sp Marmota_vancouverensis; sp Spermophilus_suslicus].
Proof. vm_compute. reflexivity. Qed.

(* No sciurid species is listed as extinct or extinct in the wild. *)
Theorem none_extinct (s : AnySpecies) : iucn (info s) <> EX /\ iucn (info s) <> EW.
Proof.
  assert (H : forall s, true = true -> negb (beq (iucn (info s)) EX) && negb (beq (iucn (info s)) EW) = true)
    by (apply enum_implies; vm_compute; reflexivity).
  specialize (H s eq_refl); rewrite andb_true_iff, !negb_true_iff in H.
  destruct H as [H1 H2]; split; intros E; [rewrite E in H1 | rewrite E in H2]; discriminate.
Qed.

(* Statuses inherited from an assessment under a former name. *)
Theorem assessed_under_former_names :
  filter (fun s => negb (String.eqb (iucn_note (info s)) "")) enum =
  [sp Sundasciurus_everetti; sp Spermophilus_alaschanicus; sp Spermophilus_nilkaensis;
   sp Spermophilopsis_leptodactyla].
Proof. vm_compute. reflexivity. Qed.
