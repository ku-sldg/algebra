Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relations.
Require Import Semigroups Groups.

Module Type RingSig.
  Parameters (Carrier: Type)(Req: relation Carrier).
  Context `{Requiv: Equivalence Carrier Req}.
  Parameter (plus: Carrier -> Carrier -> Carrier).
  Parameter (times: Carrier -> Carrier -> Carrier).
  Parameter (plus_proper: Proper (Req ==> Req ==> Req) plus).
  Parameter (times_proper: Proper (Req ==> Req ==> Req) times).
End RingSig.
