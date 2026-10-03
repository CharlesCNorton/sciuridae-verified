(******************************************************************************)
(*  Examples.v                                                                *)
(*                                                                            *)
(*  Worked identifications.  Each example is an observation as a field or    *)
(*  museum worker might record it; the identifier returns exactly the genera *)
(*  whose sourced profiles fit it (Identification.identification_exact).     *)
(******************************************************************************)

From Coq Require Import List String.
From Sciuridae Require Import Lib.Base Key.Key Key.Matrix Data.Taxonomy Data.Characters
  Data.GenusKey Identification.
Import ListNotations.
Local Open Scope string_scope.

(* Only the place of origin is known. *)
Definition from_sulawesi : Observation := observe None [("realm", "Australasia")].

(* A gliding squirrel from Malaysia, 80 mm head and body. *)
Definition tiny_glider : Observation :=
  observe (Some 80) [("realm", "Indomalaya"); ("country", "Malaysia"); ("patagium", "present")].

(* A gliding squirrel from Pakistan with the high-crowned cheek teeth that
   distinguish the woolly flying squirrels. *)
Definition woolly_glider : Observation :=
  observe (Some 500) [("realm", "Palearctic"); ("country", "Pakistan"); ("patagium", "present");
                      ("hypsodont_cheek_teeth", "yes"); ("upper_incisor_color", "yellow")].

(* A pygmy squirrel from Cameroon, 70 mm. *)
Definition african_pygmy : Observation :=
  observe (Some 70) [("realm", "Afrotropic"); ("country", "Cameroon"); ("patagium", "absent")].

(* A ground squirrel from Morocco. *)
Definition barbary_ground_squirrel : Observation :=
  observe (Some 190) [("realm", "Palearctic"); ("country", "Morocco"); ("patagium", "absent")].

(* An eastern gray squirrel collected in Pennsylvania. *)
Definition gray_squirrel_specimen : Observation :=
  observe (Some 250) [("realm", "Nearctic"); ("country", "United States"); ("patagium", "absent");
                      ("ear_tufts", "absent"); ("dorsal_stripes", "absent"); ("cheek_pouches", "absent");
                      ("manus_digit3_longest", "no"); ("baculum_well_developed", "yes")].

(* Origin alone narrows a squirrel from Sulawesi to the three Sulawesi genera,
   and by identification_exact no other genus fits. *)
Example sulawesi_candidates :
  identify_genus from_sulawesi = [Prosciurillus; Rubrisciurus; Hyosciurus].
Proof. vm_compute. reflexivity. Qed.

Example tiny_glider_is_petaurillus : identify_genus tiny_glider = [Petaurillus].
Proof. vm_compute. reflexivity. Qed.

Example woolly_glider_is_eupetaurus : identify_genus woolly_glider = [Eupetaurus].
Proof. vm_compute. reflexivity. Qed.

Example african_pygmy_is_myosciurus : identify_genus african_pygmy = [Myosciurus].
Proof. vm_compute. reflexivity. Qed.

Example barbary_ground_squirrel_is_atlantoxerus :
  identify_genus barbary_ground_squirrel = [Atlantoxerus].
Proof. vm_compute. reflexivity. Qed.

Example gray_squirrel_specimen_is_sciurus : identify_genus gray_squirrel_specimen = [Sciurus].
Proof. vm_compute. reflexivity. Qed.

(* Exactness in action: the Sulawesi observation is consistent with
   Hyosciurus, so Hyosciurus is a candidate, and it is inconsistent with
   Sciurus, so Sciurus is not. *)
Example sulawesi_excludes_sciurus : ~ In Sciurus (identify_genus from_sulawesi).
Proof. vm_compute. intros [H | [H | [H | []]]]; discriminate. Qed.
