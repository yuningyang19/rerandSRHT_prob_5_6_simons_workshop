import Problem56.PaperV6.GeneralBridgelessEarInsertion

namespace Problem56.PaperV6

/-- Break ties between incomparable old vertices without changing the strict
rank increase along any directed edge. The extra digit is an actual finite
vertex index, not an assumed topological-order certificate. -/
noncomputable def distinctDAGRank {ι ε : Type*} [Fintype ι]
    (src dst : ε → ι) (v : ι) : ℕ :=
  mingoDAGRank src dst v * (Fintype.card ι + 1) + (Fintype.equivFin ι v).1

theorem distinctDAGRank_injective {ι ε : Type*} [Fintype ι]
    (src dst : ε → ι) : Function.Injective (distinctDAGRank src dst) := by
  intro a b hab
  have ha : (Fintype.equivFin ι a).1 < Fintype.card ι + 1 := by
    exact (Fintype.equivFin ι a).2.trans (Nat.lt_succ_self _)
  have hb : (Fintype.equivFin ι b).1 < Fintype.card ι + 1 := by
    exact (Fintype.equivFin ι b).2.trans (Nat.lt_succ_self _)
  have hm := congrArg (fun n => n % (Fintype.card ι + 1)) hab
  have heq : (Fintype.equivFin ι a).1 = (Fintype.equivFin ι b).1 := by
    simpa [distinctDAGRank, Nat.add_mod, Nat.mul_mod,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hm
  exact (Fintype.equivFin ι).injective (Fin.ext heq)

theorem distinctDAGRank_edge_lt {ι ε : Type*} [Fintype ι]
    (src dst : ε → ι) (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output) (e : ε) :
    distinctDAGRank src dst (src e) < distinctDAGRank src dst (dst e) := by
  have he := hdag.edge_rank_lt src dst input output e
  have hi := (Fintype.equivFin ι (src e)).2
  unfold distinctDAGRank
  nlinarith

/-- Any two different current vertices admit an orientation compatible with
the existing DAG. Applying the concrete ear-insertion theorem in that order
does not require a separate strong-orientation or ear-decomposition axiom. -/
theorem distinctDAGRank_orders_endpoints {ι ε : Type*} [Fintype ι]
    (src dst : ε → ι) (x y : ι) (hxy : x ≠ y) :
    distinctDAGRank src dst x < distinctDAGRank src dst y ∨
      distinctDAGRank src dst y < distinctDAGRank src dst x :=
  lt_or_gt_of_ne ((distinctDAGRank_injective src dst).ne hxy)

end Problem56.PaperV6
