Require Import Lia.

From PslBase Require Import FinTypes.
Require Import UGraph.

Section VertexCoverDefinitions.
  Variable g : UGraph.
  Notation V := (V g).
  Notation E := (@E g).

  (** ** Definition of Vertex Cover *)

  (** A vertex cover is a set of vertices such that every edge has at least one endpoint in the set *)
  Definition isVertexCover (S : list V) : Prop :=
    (forall v1 v2, E (v1, v2) -> v1 el S \/ v2 el S) /\ dupfree S.

  (** A k-vertex cover is a vertex cover of size k *)
  Definition isKVertexCover (k : nat) (S : list V) : Prop :=
    |S| = k /\ isVertexCover S.

  (** ** Definition of KVertexCover Problem *)

  (** We define the KVertexCover problem as seeking a vertex cover of size k in a given graph *)
  Definition KVertexCover (i : UGraph * nat) : Prop :=
    let (g, k) := i in exists S, @isKVertexCover k S.

End VertexCoverDefinitions.
