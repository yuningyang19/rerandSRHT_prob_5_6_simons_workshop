import Problem56.PaperV6.GeneralBridgelessModifications

namespace Problem56.PaperV6

abbrev IncomingOutgoingVertex (ι : Type*) := FiberSplitVertex (fun _ : ι => Bool)

abbrev IncomingOutgoingEdge (ι ε : Type*) :=
  RootedFiberSplitEdge ε (fun _ : ι => Bool) (fun _ => false)

def incomingOutgoingSrc {ι ε : Type*} (src : ε → ι) :
    IncomingOutgoingEdge ι ε → IncomingOutgoingVertex ι :=
  rootedFiberSplitSrc src (fun _ => true) (fun _ => false)

def incomingOutgoingDst {ι ε : Type*} (dst : ε → ι) :
    IncomingOutgoingEdge ι ε → IncomingOutgoingVertex ι :=
  rootedFiberSplitDst dst (fun _ => false) (fun _ => false)

def incomingOutgoingIdentity {ι ε : Type*} (v : ι) : IncomingOutgoingEdge ι ε :=
  Sum.inr ⟨⟨v, true⟩, by simp⟩

theorem incomingOutgoing_identity_step {ι ε : Type*} (src dst : ε → ι) (v : ι) :
    directedAdjacent (incomingOutgoingSrc src) (incomingOutgoingDst dst)
      ⟨v, false⟩ ⟨v, true⟩ :=
  ⟨incomingOutgoingIdentity v, rfl, rfl⟩

theorem transGen_strict_rank {ι ε : Type*} (src dst : ε → ι) (rank : ι → ℕ)
    (hedge : ∀ e, rank (src e) < rank (dst e)) {a b : ι}
    (h : Relation.TransGen (directedAdjacent src dst) a b) : rank a < rank b := by
  induction h with
  | single hab =>
    obtain ⟨e, rfl, rfl⟩ := hab
    exact hedge e
  | tail hp hab ih =>
    obtain ⟨e, rfl, rfl⟩ := hab
    exact ih.trans (hedge e)

noncomputable def incomingOutgoingRank {ι ε : Type*} [Fintype ι]
    (src dst : ε → ι) (v : IncomingOutgoingVertex ι) : ℕ :=
  2 * mingoDAGRank src dst v.1 + if v.2 then 1 else 0

theorem incomingOutgoing_edge_rank_lt {ι ε : Type*} [Fintype ι]
    (src dst : ε → ι) (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output)
    (e : IncomingOutgoingEdge ι ε) :
    incomingOutgoingRank src dst (incomingOutgoingSrc src e) <
      incomingOutgoingRank src dst (incomingOutgoingDst dst e) := by
  cases e with
  | inl e =>
    have h := hdag.edge_rank_lt src dst input output e
    change 2 * mingoDAGRank src dst (src e) + 1 <
      2 * mingoDAGRank src dst (dst e) + 0
    omega
  | inr z =>
    rcases z with ⟨⟨v, b⟩, hb⟩
    cases b with
    | false => exact (hb rfl).elim
    | true =>
      change 2 * mingoDAGRank src dst v + 0 < 2 * mingoDAGRank src dst v + 1
      omega

theorem incomingOutgoing_lift_false {ι ε : Type*} (src dst : ε → ι)
    {a b : ι} (h : Relation.ReflTransGen (directedAdjacent src dst) a b) :
    Relation.ReflTransGen
      (directedAdjacent (incomingOutgoingSrc src) (incomingOutgoingDst dst))
      ⟨a, false⟩ ⟨b, false⟩ := by
  apply h.lift' (fun v => (⟨v, false⟩ : IncomingOutgoingVertex ι))
  intro x y hxy
  obtain ⟨e, rfl, rfl⟩ := hxy
  exact (Relation.ReflTransGen.single (incomingOutgoing_identity_step src dst (src e))).tail
    ⟨Sum.inl e, rfl, rfl⟩

theorem incomingOutgoing_lift_true {ι ε : Type*} (src dst : ε → ι)
    {a b : ι} (h : Relation.ReflTransGen (directedAdjacent src dst) a b) :
    Relation.ReflTransGen
      (directedAdjacent (incomingOutgoingSrc src) (incomingOutgoingDst dst))
      ⟨a, true⟩ ⟨b, true⟩ := by
  apply h.lift' (fun v => (⟨v, true⟩ : IncomingOutgoingVertex ι))
  intro x y hxy
  obtain ⟨e, rfl, rfl⟩ := hxy
  exact (Relation.ReflTransGen.single
    (show directedAdjacent (incomingOutgoingSrc src) (incomingOutgoingDst dst)
      ⟨src e, true⟩ ⟨dst e, false⟩ from ⟨Sum.inl e, rfl, rfl⟩)).tail
    (incomingOutgoing_identity_step src dst (dst e))

/-- Splitting every current vertex into an incoming and an outgoing copy is
an allowed rooted identity split and preserves the input-output DAG property.
The marked input is the incoming copy and the marked output the outgoing copy.
This is the local splitting operation needed when an added ear closes at one
current vertex. It has no even-degree assumption. -/
theorem incomingOutgoing_mingoAdmissibleDAG {ι ε : Type*} [Fintype ι]
    (src dst : ε → ι) (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output) :
    MingoAdmissibleDAG (incomingOutgoingSrc src) (incomingOutgoingDst dst)
      ⟨input, false⟩ ⟨output, true⟩ := by
  have hfrom : ∀ v, Relation.ReflTransGen (directedAdjacent src dst) input v := by
    intro v
    rcases hdag.2.1 v with rfl | h
    · exact Relation.ReflTransGen.refl
    · exact h.to_reflTransGen
  have hto : ∀ v, Relation.ReflTransGen (directedAdjacent src dst) v output := by
    intro v
    rcases hdag.2.2 v with rfl | h
    · exact Relation.ReflTransGen.refl
    · exact h.to_reflTransGen
  refine ⟨?_, ?_, ?_⟩
  · intro v hcycle
    exact (Nat.lt_irrefl _) (transGen_strict_rank _ _ (incomingOutgoingRank src dst)
      (incomingOutgoing_edge_rank_lt src dst input output hdag) hcycle)
  · rintro ⟨v, side⟩
    apply Relation.reflTransGen_iff_eq_or_transGen.mp
    have h := incomingOutgoing_lift_false src dst (hfrom v)
    cases side with
    | false => exact h
    | true => exact h.tail (incomingOutgoing_identity_step src dst v)
  · rintro ⟨v, side⟩
    have h : Relation.ReflTransGen
        (directedAdjacent (incomingOutgoingSrc src) (incomingOutgoingDst dst))
        ⟨v, side⟩ ⟨output, true⟩ := by
      have h := incomingOutgoing_lift_true src dst (hto v)
      cases side with
      | false => exact h.head (incomingOutgoing_identity_step src dst v)
      | true => exact h
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp h with heq | hpath
    · exact Or.inl heq.symm
    · exact Or.inr hpath

end Problem56.PaperV6
