import Problem56.PaperV6.FormalLogBasic

/-! A genuine convolution step chooses one nonempty block and partitions the
remaining positions. Forgetting that distinguished block produces the factorial
in the ordered-partition coefficient formula. -/
open scoped BigOperators
namespace Problem56.PaperV6

private theorem formalLog_mem_avoid_block
    {ι : Type*} [DecidableEq ι] {S : Finset ι}
    (P : Finpartition S) {T C : Finset ι} (hT : T ∈ P.parts) :
    C ∈ (P.avoid T).parts ↔ C ∈ P.parts ∧ C ≠ T := by
  classical
  constructor
  · intro hC
    obtain ⟨D, hD, hnDT, hdiff⟩ := (Finpartition.mem_avoid P).mp hC
    have hDT : D ≠ T := by intro h; exact hnDT (h ▸ le_rfl)
    have hdisj : Disjoint D T := P.disjoint hD hT hDT
    have hdiff' : D \ T = D := Finset.sdiff_eq_self_of_disjoint hdisj
    have hDC : D = C := hdiff' ▸ hdiff
    exact ⟨hDC ▸ hD, hDC ▸ hDT⟩
  · rintro ⟨hC, hCT⟩
    have hdisj : Disjoint C T := P.disjoint hC hT hCT
    refine (Finpartition.mem_avoid P).mpr ⟨C, hC, ?_, ?_⟩
    · intro hle
      exact P.ne_empty hC (disjoint_self.mp (hdisj.mono le_rfl hle))
    · exact Finset.sdiff_eq_self_of_disjoint hdisj

theorem formalLog_avoid_parts
    {ι : Type*} [DecidableEq ι] {S : Finset ι}
    (P : Finpartition S) {T : Finset ι} (hT : T ∈ P.parts) :
    (P.avoid T).parts = P.parts.erase T := by
  ext C
  simp only [formalLog_mem_avoid_block P hT, Finset.mem_erase]
  tauto

abbrev FormalLogNonemptySubset {ι : Type*} (S : Finset ι) :=
  {T : S.powerset // T.1.Nonempty}

abbrev FormalLogSplit {ι : Type*} [DecidableEq ι] (S : Finset ι) :=
  Σ T : FormalLogNonemptySubset S, Finpartition (S \ T.1.1)

noncomputable def formalLogInsertBlock
    {ι : Type*} [DecidableEq ι] {S : Finset ι}
    (T : FormalLogNonemptySubset S) (Q : Finpartition (S \ T.1.1)) : Finpartition S :=
  Q.extend T.2.ne_empty (by
      rw [Finset.disjoint_left]
      intro x hx hT
      exact (Finset.mem_sdiff.mp hx).2 hT)
    (Finset.sdiff_union_of_subset (Finset.mem_powerset.mp T.1.2))

@[simp] theorem formalLogInsertBlock_parts
    {ι : Type*} [DecidableEq ι] {S : Finset ι}
    (T : FormalLogNonemptySubset S) (Q : Finpartition (S \ T.1.1)) :
    (formalLogInsertBlock T Q).parts = insert T.1.1 Q.parts := rfl

theorem formalLogInsertBlock_notMem
    {ι : Type*} [DecidableEq ι] {S : Finset ι}
    (T : FormalLogNonemptySubset S) (Q : Finpartition (S \ T.1.1)) :
    T.1.1 ∉ Q.parts := by
  intro h
  obtain ⟨x, hx⟩ := T.2
  exact (Finset.mem_sdiff.mp (Q.subset h hx)).2 hx

theorem formalLogInsertBlock_avoid
    {ι : Type*} [DecidableEq ι] {S : Finset ι}
    (T : FormalLogNonemptySubset S) (Q : Finpartition (S \ T.1.1)) :
    (formalLogInsertBlock T Q).avoid T.1.1 = Q := by
  ext C
  rw [formalLog_avoid_parts _ (by simp), formalLogInsertBlock_parts,
    Finset.erase_insert (formalLogInsertBlock_notMem T Q)]

noncomputable def formalLogPointedOfSplit
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (x : FormalLogSplit S) :
    Σ P : Finpartition S, P.parts :=
  ⟨formalLogInsertBlock x.1 x.2, ⟨x.1.1.1, by simp⟩⟩

theorem formalLogPointedOfSplit_injective
    {ι : Type*} [DecidableEq ι] (S : Finset ι) :
    Function.Injective (formalLogPointedOfSplit S) := by
  rintro ⟨T, Q⟩ ⟨U, R⟩ h
  have hTU : T = U := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : Σ P : Finpartition S, P.parts ↦ x.2.1) h
  cases hTU
  have hP : formalLogInsertBlock T Q = formalLogInsertBlock T R := congrArg Sigma.fst h
  have hQ : Q = R := by
    have := congrArg (fun P : Finpartition S ↦ P.avoid T.1.1) hP
    simpa only [formalLogInsertBlock_avoid] using this
  cases hQ
  rfl

theorem formalLogPointedOfSplit_surjective
    {ι : Type*} [DecidableEq ι] (S : Finset ι) :
    Function.Surjective (formalLogPointedOfSplit S) := by
  rintro ⟨P, T⟩
  let U : FormalLogNonemptySubset S :=
    ⟨⟨T.1, Finset.mem_powerset.mpr (P.subset T.2)⟩, P.nonempty_of_mem_parts T.2⟩
  let Q : Finpartition (S \ U.1.1) := P.avoid T.1
  have hP : formalLogInsertBlock U Q = P := by
    ext C
    rw [formalLogInsertBlock_parts]
    change C ∈ insert T.1 (P.avoid T.1).parts ↔ C ∈ P.parts
    rw [formalLog_avoid_parts P T.2, Finset.insert_erase T.2]
  refine ⟨⟨U, Q⟩, ?_⟩
  apply Sigma.ext hP
  apply (Subtype.heq_iff_coe_eq (fun C ↦ by
    change C ∈ (formalLogInsertBlock U Q).parts ↔ C ∈ P.parts
    rw [hP])).mpr
  rfl

noncomputable def formalLogSplitEquivPointed
    {ι : Type*} [DecidableEq ι] (S : Finset ι) :
    FormalLogSplit S ≃ (Σ P : Finpartition S, P.parts) :=
  Equiv.ofBijective (formalLogPointedOfSplit S)
    ⟨formalLogPointedOfSplit_injective S, formalLogPointedOfSplit_surjective S⟩

end Problem56.PaperV6
