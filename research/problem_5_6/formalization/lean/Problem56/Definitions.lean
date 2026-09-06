import Mathlib

/-!
Primitive finite objects for the statement layer of the Problem 5.6
formalization.  The probability laws below are finite sums, so the public
statements do not rely on measure-theoretic representatives.
-/

open scoped BigOperators Matrix

namespace Problem56

abbrev WalshIndex (m : ℕ) := Fin m → ZMod 2

abbrev SignLayer (α : Type*) := α → Bool

def walshCard (m : ℕ) : ℕ := Fintype.card (WalshIndex m)

def walshDot {m : ℕ} (a b : WalshIndex m) : ZMod 2 :=
  ∑ i, a i * b i

def walshCharacter {m : ℕ} (a b : WalshIndex m) : ℝ :=
  if walshDot a b = 0 then 1 else -1

noncomputable def normalizedWalsh (m : ℕ) :
    Matrix (WalshIndex m) (WalshIndex m) ℝ :=
  fun a b ↦ walshCharacter a b / Real.sqrt (walshCard m : ℝ)

def signValue {α : Type*} (d : SignLayer α) (i : α) : ℝ :=
  if d i then -1 else 1

def signDiagonal {α : Type*} [DecidableEq α] (d : SignLayer α) : Matrix α α ℝ :=
  Matrix.diagonal (signValue d)

abbrev FixedSubset (α : Type*) [Fintype α] [DecidableEq α] (k : ℕ) :=
  {J : Finset α // J.card = k}

def sampleMatrix {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (J : FixedSubset α k) : Matrix α {i // i ∈ J.1} ℝ :=
  fun i j ↦ if i = j.1 then 1 else 0

def coordinateProjection {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (J : FixedSubset α k) : Matrix α α ℝ :=
  Matrix.diagonal (fun i ↦ if i ∈ J.1 then 1 else 0)

noncomputable def rerandomizedSRHT {m k : ℕ}
    (d₁ d₂ : SignLayer (WalshIndex m)) (J : FixedSubset (WalshIndex m) k) :
    Matrix (WalshIndex m) {i // i ∈ J.1} ℝ :=
  Real.sqrt ((walshCard m : ℝ) / (k : ℝ)) •
    (signDiagonal d₁ * normalizedWalsh m * signDiagonal d₂ *
      normalizedWalsh m * sampleMatrix J)

def OrthonormalFrame {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (V : Matrix α (Fin r) ℝ) : Prop :=
  V.transpose * V = 1

noncomputable def transformedFrame {m r : ℕ}
    (d₁ d₂ : SignLayer (WalshIndex m)) (V : Matrix (WalshIndex m) (Fin r) ℝ) :
    Matrix (WalshIndex m) (Fin r) ℝ :=
  normalizedWalsh m * signDiagonal d₂ * normalizedWalsh m * signDiagonal d₁ * V

noncomputable def randomProjection {m r : ℕ}
    (d₁ d₂ : SignLayer (WalshIndex m)) (V : Matrix (WalshIndex m) (Fin r) ℝ) :
    Matrix (WalshIndex m) (WalshIndex m) ℝ :=
  let X := transformedFrame d₁ d₂ V
  X * X.transpose

noncomputable def compressedGram {m r k : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (d₁ d₂ : SignLayer (WalshIndex m)) (J : FixedSubset (WalshIndex m) k) :
    Matrix (Fin r) (Fin r) ℝ :=
  let Ω := rerandomizedSRHT d₁ d₂ J
  V.transpose * Ω * Ω.transpose * V

noncomputable def euclideanNorm {α : Type*} [Fintype α] (x : α → ℝ) : ℝ :=
  Real.sqrt (∑ i, (x i) ^ 2)

noncomputable def euclideanOperatorNorm {α β : Type*}
    [Fintype α] [Fintype β] (A : Matrix α β ℝ) : ℝ :=
  sSup {z : ℝ | ∃ x : β → ℝ, euclideanNorm x = 1 ∧
    z = euclideanNorm (A.mulVec x)}

noncomputable def uniformProbability {Ω : Type*} [Fintype Ω]
    (event : Ω → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter event).card : ℝ) / (Fintype.card Ω : ℝ)

noncomputable def uniformExpectation {Ω : Type*} [Fintype Ω]
    (Y : Ω → ℝ) : ℝ :=
  (∑ ω, Y ω) / (Fintype.card Ω : ℝ)

noncomputable def bernoulliWeight {α : Type*} [Fintype α] [DecidableEq α]
    (θ : ℝ) (e : SignLayer α) : ℝ :=
  ∏ i, if e i then θ else 1 - θ

noncomputable def bernoulliProbability {α : Type*} [Fintype α] [DecidableEq α]
    (θ : ℝ) (event : SignLayer α → Prop) : ℝ := by
  classical
  exact ∑ e, if event e then bernoulliWeight θ e else 0

noncomputable def bernoulliExpectation {α : Type*} [Fintype α] [DecidableEq α]
    (θ : ℝ) (Y : SignLayer α → ℝ) : ℝ := by
  classical
  exact ∑ e, bernoulliWeight θ e * Y e

def bernoulliProjection {α : Type*} [Fintype α] [DecidableEq α]
    (e : SignLayer α) : Matrix α α ℝ :=
  Matrix.diagonal (fun i ↦ if e i then 1 else 0)

noncomputable def frameFailureProbability {m r k : ℕ}
    (ε : ℝ) (V : Matrix (WalshIndex m) (Fin r) ℝ) : ℝ :=
  uniformProbability (Ω := SignLayer (WalshIndex m) ×
      SignLayer (WalshIndex m) × FixedSubset (WalshIndex m) k)
    (fun ω ↦ euclideanOperatorNorm
      (compressedGram V ω.1 ω.2.1 ω.2.2 - 1) > ε)

noncomputable def spectralFailureSup (m r k : ℕ) (ε : ℝ) : ℝ :=
  sSup {z : ℝ | ∃ V : Matrix (WalshIndex m) (Fin r) ℝ,
    OrthonormalFrame V ∧ z = frameFailureProbability (k := k) ε V}

noncomputable def fixedSampleGram {α : Type*} [Fintype α] [DecidableEq α]
    {r k : ℕ} (X : Matrix α (Fin r) ℝ) (J : FixedSubset α k) :
    Matrix (Fin r) (Fin r) ℝ :=
  ((Fintype.card α : ℝ) / (k : ℝ)) •
    (X.transpose * coordinateProjection J * X)

noncomputable def bernoulliGram {α : Type*} [Fintype α] [DecidableEq α]
    {r : ℕ} (θ : ℝ) (X : Matrix α (Fin r) ℝ) (e : SignLayer α) :
    Matrix (Fin r) (Fin r) ℝ :=
  θ⁻¹ • (X.transpose * bernoulliProjection e * X)

noncomputable def frobeniusNormSq {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α β ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

noncomputable def signPairExpectation {α : Type*} [Fintype α] [DecidableEq α]
    (Y : SignLayer α → SignLayer α → ℝ) : ℝ :=
  uniformExpectation (Ω := SignLayer α × SignLayer α) (fun d ↦ Y d.1 d.2)

noncomputable def signBernoulliExpectation {α : Type*}
    [Fintype α] [DecidableEq α] (θ : ℝ)
    (Y : SignLayer α → SignLayer α → SignLayer α → ℝ) : ℝ :=
  signPairExpectation fun d₁ d₂ ↦ bernoulliExpectation θ (Y d₁ d₂)

noncomputable def uniformBernoulliFailureProbability
    {Ω α : Type*} [Fintype Ω] [Fintype α] [DecidableEq α]
    {r : ℕ} (θ η : ℝ) (X : Ω → Matrix α (Fin r) ℝ) : ℝ :=
  uniformExpectation (fun ω ↦
    bernoulliProbability θ (fun e ↦
      euclideanOperatorNorm (bernoulliGram θ (X ω) e - 1) > η))

noncomputable def uniformFixedFailureProbability
    {Ω α : Type*} [Fintype Ω] [Fintype α] [DecidableEq α]
    {r k : ℕ} (ε : ℝ) (X : Ω → Matrix α (Fin r) ℝ) : ℝ :=
  uniformProbability (Ω := Ω × FixedSubset α k) (fun sample ↦
    euclideanOperatorNorm (fixedSampleGram (X sample.1) sample.2 - 1) > ε)

noncomputable def jointCumulantOn {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    [DecidableEq ι] (Y : ι → Ω → ℝ) : ℝ :=
  ∑ P : Finpartition (Finset.univ : Finset ι),
    ((-1 : ℝ) ^ (P.parts.card - 1) * (Nat.factorial (P.parts.card - 1) : ℝ)) *
      ∏ B ∈ P.parts, uniformExpectation (fun ω ↦ ∏ j ∈ B, Y j ω)

noncomputable def jointCumulant {Ω : Type*} [Fintype Ω] {q : ℕ}
    (Y : Fin q → Ω → ℝ) : ℝ :=
  jointCumulantOn Y

def ProductPartitionConnected {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ τ : Finpartition (Finset.univ : Finset ι)) : Prop :=
  ∀ i j, Relation.ReflTransGen
    (fun a b ↦ σ.part a = σ.part b ∨ τ.part a = τ.part b) i j

noncomputable def partitionCumulantProduct
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (Y : ι → Ω → ℝ) (σ : Finpartition (Finset.univ : Finset ι)) : ℝ :=
  ∏ B ∈ σ.parts, jointCumulantOn (fun j : B ↦ Y j.1)

noncomputable def connectedPartitionCumulantSum
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (Y : ι → Ω → ℝ) (τ : Finpartition (Finset.univ : Finset ι)) : ℝ := by
  classical
  exact ∑ σ : Finpartition (Finset.univ : Finset ι),
    if ProductPartitionConnected σ τ then partitionCumulantProduct Y σ else 0

def cyclicSucc {q : ℕ} (i : Fin q) : Fin q :=
  ⟨(i.1 + 1) % q, Nat.mod_lt _ (Nat.pos_of_ne_zero fun h ↦ by
    subst q
    exact Fin.elim0 i)⟩

def equalityEdgeMultiplicity {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q)))
    (B C : Finset (Fin q)) : ℕ :=
  ((Finset.univ : Finset (Fin q)).filter fun i ↦
    (P.part i = B ∧ P.part (cyclicSucc i) = C) ∨
      (P.part i = C ∧ P.part (cyclicSucc i) = B)).card

def equalityLoopOccurrences {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q))) : ℕ :=
  ((Finset.univ : Finset (Fin q)).filter fun i ↦
    P.part i = P.part (cyclicSucc i)).card

def equalityOddIncidentVertices {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q))) : Finset (Finset (Fin q)) :=
  P.parts.filter fun B ↦ ∃ C ∈ P.parts,
    B ≠ C ∧ Odd (equalityEdgeMultiplicity P B C)

def graphAdjacent {ι ε : Type*} (src dst : ε → ι) (u v : ι) : Prop :=
  ∃ e, (src e = u ∧ dst e = v) ∨ (src e = v ∧ dst e = u)

def GraphConnected {ι ε : Type*} (src dst : ε → ι) : Prop :=
  ∀ u v, Relation.ReflTransGen (graphAdjacent src dst) u v

abbrev EqualityVertex {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q))) :=
  {B : Finset (Fin q) // B ∈ P.parts}

def equalityVertexAt {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q))) (i : Fin q) : EqualityVertex P :=
  ⟨P.part i, P.part_mem.2 (Finset.mem_univ i)⟩

def equalityExceptionalVertices {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q))) : Finset (Finset (Fin q)) :=
  equalityOddIncidentVertices P ∪ P.parts.filter (fun B ↦ 2 < B.card)

def equalityExceptionalDegree {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q))) : ℕ :=
  ∑ B ∈ equalityExceptionalVertices P, 2 * B.card

def equalityLoopsAt {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q))) (B : Finset (Fin q)) : ℕ :=
  ((Finset.univ : Finset (Fin q)).filter fun i ↦
    P.part i = B ∧ P.part (cyclicSucc i) = B).card

def IsEqualityInternal {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q))) (B : Finset (Fin q)) : Prop :=
  equalityLoopsAt P B = 0 ∧
  ∃ C ∈ P.parts, ∃ D ∈ P.parts, C ≠ D ∧ C ≠ B ∧ D ≠ B ∧
    equalityEdgeMultiplicity P B C = 2 ∧
    equalityEdgeMultiplicity P B D = 2 ∧
    ∀ A ∈ P.parts, A ≠ B → A ≠ C → A ≠ D →
      equalityEdgeMultiplicity P B A = 0

def IsEqualityLoopTerminal {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q))) (B : Finset (Fin q)) : Prop :=
  equalityLoopsAt P B = 1 ∧
  ∃ C ∈ P.parts, C ≠ B ∧ equalityEdgeMultiplicity P B C = 2 ∧
    ∀ A ∈ P.parts, A ≠ B → A ≠ C → equalityEdgeMultiplicity P B A = 0

def IsEqualityFourEdgeTerminal {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q))) (B : Finset (Fin q)) : Prop :=
  equalityLoopsAt P B = 0 ∧
  ∃ C ∈ P.parts, C ≠ B ∧ equalityEdgeMultiplicity P B C = 4 ∧
    ∀ A ∈ P.parts, A ≠ B → A ≠ C → equalityEdgeMultiplicity P B A = 0

abbrev SelectorEqualityData (p s t : ℕ) :=
  {P : Finpartition (Finset.univ : Finset (Fin (2 * p))) //
    (∀ B ∈ P.parts, 2 ≤ B.card) ∧
    P.parts.card = p - s ∧
    (equalityOddIncidentVertices P).card = t}

abbrev Pairing {α : Type*} [DecidableEq α] (S : Finset α) :=
  {P : Finpartition S // ∀ B ∈ P.parts, B.card = 2}

abbrev LargeBlockPattern (p d : ℕ) :=
  {SP : (S : Finset (Fin (2 * p))) × Finpartition S //
    (∀ B ∈ SP.2.parts, 3 ≤ B.card) ∧
    (∑ B ∈ SP.2.parts, (B.card - 2)) = 2 * d}

abbrev DisjointPairPattern (p s h : ℕ) :=
  {USP : (U : Finset (Fin (2 * p))) ×
      (S : Finset (Fin (2 * p))) × Pairing S //
    USP.1.card ≤ 4 * h ∧ USP.2.1.card ≤ 8 * h + 2 * s}

structure OccurrencePartitionData (q : ℕ) where
  middle : Finpartition (Finset.univ : Finset (Fin (2 * q)))
  input : Finpartition (Finset.univ : Finset (Fin (2 * q)))

abbrev ProductOccurrence (q : ℕ) := Fin (2 * q) ⊕ Fin (2 * q)

def leftOccurrence {q : ℕ} (f : Fin q) : Fin (2 * q) :=
  ⟨2 * f.1, by omega⟩

def rightOccurrence {q : ℕ} (f : Fin q) : Fin (2 * q) :=
  ⟨2 * f.1 + 1, by omega⟩

def productJoinRelated {q : ℕ} (D : OccurrencePartitionData q)
    (x y : ProductOccurrence q) : Prop :=
  match x, y with
  | Sum.inl a, Sum.inl b => D.middle.part a = D.middle.part b
  | Sum.inr a, Sum.inr b =>
      D.input.part a = D.input.part b ∨
        ∃ f : Fin q, (a = leftOccurrence f ∧ b = rightOccurrence f) ∨
          (b = leftOccurrence f ∧ a = rightOccurrence f)
  | Sum.inl a, Sum.inr b =>
      ∃ f : Fin q, (a = leftOccurrence f ∧ b = leftOccurrence f) ∨
        (a = rightOccurrence f ∧ b = rightOccurrence f)
  | Sum.inr a, Sum.inl b =>
      ∃ f : Fin q, (b = leftOccurrence f ∧ a = leftOccurrence f) ∨
        (b = rightOccurrence f ∧ a = rightOccurrence f)

def ProductOccurrenceConnected {q : ℕ} (D : OccurrencePartitionData q) : Prop :=
  ∀ x y, Relation.ReflTransGen (productJoinRelated D) x y

abbrev OccurrenceVertex {q : ℕ} (D : OccurrencePartitionData q) :=
  EqualityVertex D.middle ⊕ EqualityVertex D.input

abbrev OccurrenceEdge (q : ℕ) := Fin q × Fin 3

def occurrenceSrc {q : ℕ} (D : OccurrencePartitionData q) :
    OccurrenceEdge q → OccurrenceVertex D
  | (f, e) => if e.1 = 0 then Sum.inl (equalityVertexAt D.middle (leftOccurrence f))
      else Sum.inr (equalityVertexAt D.input
        (if e.1 = 1 then leftOccurrence f else rightOccurrence f))

def occurrenceDst {q : ℕ} (D : OccurrencePartitionData q) :
    OccurrenceEdge q → OccurrenceVertex D
  | (f, e) => if e.1 = 2 then Sum.inl (equalityVertexAt D.middle (rightOccurrence f))
      else Sum.inr (equalityVertexAt D.input
        (if e.1 = 0 then leftOccurrence f else rightOccurrence f))

def IsSurvivingOccurrencePartition {q : ℕ} (D : OccurrencePartitionData q) : Prop :=
  (∀ B ∈ D.middle.parts, 0 < B.card ∧ Even B.card) ∧
  (∀ B ∈ D.input.parts, 0 < B.card ∧ Even B.card) ∧
  GraphConnected (occurrenceSrc D) (occurrenceDst D)

noncomputable def occurrenceContraction {m r q : ℕ}
    (D : OccurrencePartitionData q)
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (i j : Fin q → WalshIndex m) : ℝ :=
  ∑ labels : OccurrenceVertex D → WalshIndex m,
    (∏ f,
      normalizedWalsh m (labels (Sum.inl (equalityVertexAt D.middle (leftOccurrence f))))
        (labels (Sum.inr (equalityVertexAt D.input (leftOccurrence f)))) *
      (V * V.transpose)
        (labels (Sum.inr (equalityVertexAt D.input (leftOccurrence f))))
        (labels (Sum.inr (equalityVertexAt D.input (rightOccurrence f)))) *
      normalizedWalsh m
        (labels (Sum.inr (equalityVertexAt D.input (rightOccurrence f))))
        (labels (Sum.inl (equalityVertexAt D.middle (rightOccurrence f))))) *
    ∏ B : EqualityVertex D.middle,
      ∏ f,
        (if leftOccurrence f ∈ B.1 then walshCharacter (i f) (labels (Sum.inl B)) else 1) *
        (if rightOccurrence f ∈ B.1 then walshCharacter (j f) (labels (Sum.inl B)) else 1)

noncomputable def walshFinEquiv (m : ℕ) :
    WalshIndex m ≃ Fin (walshCard m) := Fintype.equivFin _

noncomputable def transportedFrame {m r : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) :
    Matrix (Fin (walshCard m)) (Fin r) ℝ :=
  fun a j ↦ V ((walshFinEquiv m).symm a) j

noncomputable def occurrenceEdgeMatrix {m r q : ℕ}
    (D : OccurrencePartitionData q)
    (V : Matrix (WalshIndex m) (Fin r) ℝ) :
    ∀ e : OccurrenceEdge q,
      Matrix (Fin (walshCard m)) (Fin (walshCard m)) ℝ :=
  fun e a b ↦
    if e.2.1 = 1 then
      (V * V.transpose) ((walshFinEquiv m).symm a) ((walshFinEquiv m).symm b)
    else
      normalizedWalsh m ((walshFinEquiv m).symm a) ((walshFinEquiv m).symm b)

noncomputable def occurrenceVertexWeight {m q : ℕ}
    (D : OccurrencePartitionData q)
    (i j : Fin q → WalshIndex m) :
    OccurrenceVertex D → Fin (walshCard m) → ℝ
  | Sum.inl B, a =>
      ∏ f,
        (if leftOccurrence f ∈ B.1 then
          walshCharacter (i f) ((walshFinEquiv m).symm a) else 1) *
        (if rightOccurrence f ∈ B.1 then
          walshCharacter (j f) ((walshFinEquiv m).symm a) else 1)
  | Sum.inr _, _ => 1

abbrev EvenOccurrencePartition (q : ℕ) :=
  {P : Finpartition (Finset.univ : Finset (Fin (2 * q))) //
    ∀ B ∈ P.parts, Even B.card}

noncomputable def rademacherCumulant (b : ℕ) : ℝ :=
  jointCumulant (Ω := Bool) (q := b) (fun _ ξ ↦ if ξ then -1 else 1)

def translateSign {m : ℕ} (s : WalshIndex m)
    (d : SignLayer (WalshIndex m)) : SignLayer (WalshIndex m) :=
  fun i ↦ d (i + s)

noncomputable def modulateSign {m : ℕ} (s : WalshIndex m)
    (d : SignLayer (WalshIndex m)) : SignLayer (WalshIndex m) :=
  fun i ↦ if walshCharacter s i = 1 then d i else !(d i)

def walshModulation {m : ℕ} (s : WalshIndex m) :
    Matrix (WalshIndex m) (WalshIndex m) ℝ :=
  Matrix.diagonal (walshCharacter s)

def walshTranslation {m : ℕ} (s : WalshIndex m) :
    Matrix (WalshIndex m) (WalshIndex m) ℝ :=
  fun i j ↦ if i = j + s then 1 else 0

structure ContractedCoreCode (p a : ℕ) where
  vertexDegreeChoice : Fin ((4 * p + 1) ^ a)
  degreeVector : Fin (8 * a) → Fin (4 * p + 1)
  halfEdgePairing : Fin (18 * a) → Fin (4 * p + 1)
  doubledLinkPorts : Fin (36 * a) → Fin (4 * p + 1)
  linkLengths : Fin (9 * a) → Fin (4 * p + 1)
  deriving Fintype

structure EulerTransitionCode (p a : ℕ) where
  startingDirectedEdgeAndCase : Fin (8 * p)
  localDegreeFourTransitions : Fin p → Fin 3
  excessTransitions : Fin (2 * a) → Fin (4 * p + 1)
  deriving Fintype

abbrev EulerTransitions {p a : ℕ} (_ : ContractedCoreCode p a) :=
  EulerTransitionCode p a

structure EqualityEncoding (p s t : ℕ) where
  encodeCore : SelectorEqualityData p s t → ContractedCoreCode p (s + t)
  encodeTransition : (Q : SelectorEqualityData p s t) → EulerTransitions (encodeCore Q)
  decode : (c : ContractedCoreCode p (s + t)) →
    EulerTransitions c → Option (SelectorEqualityData p s t)
  decode_encode : ∀ Q, decode (encodeCore Q) (encodeTransition Q) = some Q

def occurrenceWithinVertices {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (U : Finset (EqualityVertex Q.1)) : Finset (Fin (2 * p)) :=
  (Finset.univ : Finset (Fin (2 * p))).filter fun e ↦
    equalityVertexAt Q.1 e ∈ U ∧ equalityVertexAt Q.1 (cyclicSucc e) ∈ U

abbrev DisjointPairChoice {p s t : ℕ} (Q : SelectorEqualityData p s t) (h : ℕ) :=
  (U : {U : Finset (EqualityVertex Q.1) // U.card ≤ 4 * h}) ×
    (S : {S : Finset (Fin (2 * p)) // S ⊆ occurrenceWithinVertices Q U.1}) ×
      Pairing S.1

structure EntryCumulantPartitionData (p s t : ℕ) where
  selector : SelectorEqualityData p s t
  entry : Finpartition (Finset.univ : Finset (Fin (2 * p)))

abbrev EntryBlock {p s t : ℕ} (D : EntryCumulantPartitionData p s t) :=
  {B : Finset (Fin (2 * p)) // B ∈ D.entry.parts}

def IsSurvivingEntryPairBlock {p s t : ℕ}
    (D : EntryCumulantPartitionData p s t) (B : Finset (Fin (2 * p))) : Prop :=
  B.card = 2 → ∀ e ∈ B, ∀ f ∈ B, e ≠ f →
    let srcE := equalityVertexAt D.selector.1 e
    let dstE := equalityVertexAt D.selector.1 (cyclicSucc e)
    let srcF := equalityVertexAt D.selector.1 f
    let dstF := equalityVertexAt D.selector.1 (cyclicSucc f)
    (srcE = dstE ∧ srcF = dstF) ∨
    (srcE ≠ dstE ∧ srcF ≠ dstF ∧
      ((srcE = srcF ∧ dstE = dstF) ∨ (srcE = dstF ∧ dstE = srcF))) ∨
    (srcE ≠ dstE ∧ srcF ≠ dstF ∧
      Disjoint ({srcE, dstE} : Finset (EqualityVertex D.selector.1))
        ({srcF, dstF} : Finset (EqualityVertex D.selector.1)))

def AdmissibleEntryPairBlocks {p s t : ℕ}
    (D : EntryCumulantPartitionData p s t) : Prop :=
  ∀ B ∈ D.entry.parts, IsSurvivingEntryPairBlock D B

def entryPartitionData {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (P : Finpartition (Finset.univ : Finset (Fin (2 * p)))) :
    EntryCumulantPartitionData p s t :=
  { selector := Q, entry := P }

noncomputable def entryConstraintMatrix {p s t : ℕ}
    (D : EntryCumulantPartitionData p s t) :
    Matrix (EntryBlock D) (EqualityVertex D.selector.1) (ZMod 2) :=
  fun B u ↦ ∑ e ∈ B.1, ((if equalityVertexAt D.selector.1 e = u then 1 else 0) +
    (if equalityVertexAt D.selector.1 (cyclicSucc e) = u then 1 else 0))

abbrev AggregateEntryPartition {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (d h : ℕ) :=
  {P : Finpartition (Finset.univ : Finset (Fin (2 * p))) //
    (∀ B ∈ P.parts, 2 ≤ B.card) ∧
    AdmissibleEntryPairBlocks (entryPartitionData Q P) ∧
    P.parts.card = p - d ∧
    Matrix.rank (entryConstraintMatrix (entryPartitionData Q P)) = h}

def entryPartitionCumulantConstant {p : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin (2 * p)))) : ℕ :=
  ∏ B ∈ P.parts, (2 * B.card) ^ (12 * B.card)

noncomputable def aggregateEntryPartitionCumulantSum {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (d h : ℕ) : ℕ := by
  classical
  exact ∑ P : AggregateEntryPartition Q d h, entryPartitionCumulantConstant P.1

def largeBlockOccurrences {p s t : ℕ}
    (D : EntryCumulantPartitionData p s t) : Finset (Fin (2 * p)) :=
  Finset.univ.filter fun e ↦ 3 ≤ (D.entry.part e).card

def largeTouchedVertices {p s t : ℕ}
    (D : EntryCumulantPartitionData p s t) :
    Finset (EqualityVertex D.selector.1) :=
  Finset.univ.filter fun u ↦ ∃ e ∈ largeBlockOccurrences D,
    equalityVertexAt D.selector.1 e = u ∨
      equalityVertexAt D.selector.1 (cyclicSucc e) = u

noncomputable def disjointPairRows {p s t : ℕ}
    (D : EntryCumulantPartitionData p s t) : Finset (EntryBlock D) :=
  Finset.univ.filter fun B ↦
    (Finset.univ.filter fun u ↦ entryConstraintMatrix D B u ≠ 0).card = 4

noncomputable def disjointConstraintMatrix {p s t : ℕ}
    (D : EntryCumulantPartitionData p s t) :
    Matrix (EntryBlock D) (EqualityVertex D.selector.1) (ZMod 2) :=
  fun B u ↦ if B ∈ disjointPairRows D then entryConstraintMatrix D B u else 0

noncomputable def disjointConstraintSupport {p s t : ℕ}
    (D : EntryCumulantPartitionData p s t) :
    Finset (EqualityVertex D.selector.1) :=
  Finset.univ.filter fun u ↦ ∃ B, disjointConstraintMatrix D B u ≠ 0

def oddIncidentVertexSet {p s t : ℕ}
    (D : EntryCumulantPartitionData p s t) :
    Finset (EqualityVertex D.selector.1) :=
  Finset.univ.filter fun u ↦ u.1 ∈ equalityOddIncidentVertices D.selector.1

noncomputable def euclideanInner {α : Type*} [Fintype α]
    (x y : α → ℝ) : ℝ :=
  ∑ i, x i * y i

noncomputable def quadraticForm {α : Type*} [Fintype α]
    (A : Matrix α α ℝ) (x : α → ℝ) : ℝ :=
  euclideanInner x (A.mulVec x)

noncomputable def orthogonalConjugate {α : Type*} [Fintype α]
    (Q A : Matrix α α ℝ) : Matrix α α ℝ :=
  Q.transpose * A * Q

def IsTwoProjectionBlockDecomposition {α : Type*} [Fintype α] [DecidableEq α]
    (P E Q : Matrix α α ℝ) (block : α → α) : Prop :=
  Q.transpose * Q = 1 ∧ Q * Q.transpose = 1 ∧
  (∀ i, ((Finset.univ : Finset α).filter fun j ↦ block j = block i).card ≤ 2) ∧
  (∀ i j, block i ≠ block j →
    orthogonalConjugate Q P i j = 0 ∧ orthogonalConjugate Q E i j = 0) ∧
  (∀ i, ((Finset.univ : Finset α).filter fun j ↦ block j = block i).card = 1 →
    orthogonalConjugate Q P i i ∈ ({0, 1} : Set ℝ) ∧
    orthogonalConjugate Q E i i ∈ ({0, 1} : Set ℝ)) ∧
  (∀ i, ((Finset.univ : Finset α).filter fun j ↦ block j = block i).card = 2 →
    ∃ j, j ≠ i ∧ block j = block i ∧
      ∃ lam : ℝ, 0 < lam ∧ lam < 1 ∧
        orthogonalConjugate Q P i j = 0 ∧ orthogonalConjugate Q P j i = 0 ∧
        orthogonalConjugate Q E i j = Real.sqrt (lam * (1 - lam)) ∧
        orthogonalConjugate Q E j i = Real.sqrt (lam * (1 - lam)) ∧
        ((orthogonalConjugate Q P i i = 1 ∧ orthogonalConjugate Q P j j = 0 ∧
          orthogonalConjugate Q E i i = lam ∧
          orthogonalConjugate Q E j j = 1 - lam) ∨
         (orthogonalConjugate Q P j j = 1 ∧ orthogonalConjugate Q P i i = 0 ∧
          orthogonalConjugate Q E j j = lam ∧
          orthogonalConjugate Q E i i = 1 - lam)))

noncomputable def selectorEqualityCount (p s t : ℕ) : ℕ := by
  classical
  exact Fintype.card (SelectorEqualityData p s t)

def directedAdjacent {ι ε : Type*} (src dst : ε → ι) (u v : ι) : Prop :=
  ∃ e, src e = u ∧ dst e = v

def MingoAdmissibleDAG {ι ε : Type*} (src dst : ε → ι)
    (input output : ι) : Prop :=
  (∀ v, ¬ Relation.TransGen (directedAdjacent src dst) v v) ∧
  (∀ v, v = input ∨ Relation.TransGen (directedAdjacent src dst) input v) ∧
  (∀ v, v = output ∨ Relation.TransGen (directedAdjacent src dst) v output)

def graphDegree {ι ε : Type*} [Fintype ε] [DecidableEq ι]
    (src dst : ε → ι) (v : ι) : ℕ :=
  (Finset.univ.filter fun e ↦ src e = v).card +
    (Finset.univ.filter fun e ↦ dst e = v).card

noncomputable def graphContraction {ι ε : Type*}
    [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (w : ∀ v, Fin (dim v) → ℝ) : ℝ :=
  ∑ labels : ∀ v, Fin (dim v),
    (∏ e, M e (labels (src e)) (labels (dst e))) *
      ∏ v, w v (labels v)

noncomputable def graphOperator {ι ε : Type*}
    [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input output : ι) : Matrix (Fin (dim input)) (Fin (dim output)) ℝ :=
  fun a b ↦ ∑ labels : ∀ v, Fin (dim v),
    if labels input = a ∧ labels output = b then
      ∏ e, M e (labels (src e)) (labels (dst e))
    else 0

def IsOrthogonalProjection {α : Type*} [Fintype α] [DecidableEq α]
    (P : Matrix α α ℝ) : Prop :=
  P.transpose = P ∧ P * P = P

def HasRankProjectionEdge {ι ε : Type*} [Fintype ι] [Fintype ε]
    [DecidableEq ι] (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (r : ℕ) : Prop :=
  ∃ (e₀ : ε) (n : ℕ) (V : Matrix (Fin n) (Fin r) ℝ),
    dim (src e₀) = n ∧ dim (dst e₀) = n ∧
    OrthonormalFrame V ∧ HEq (M e₀) (V * V.transpose)

def K₂ : ℕ := 4 ^ 24
def K₀ : ℕ := 576 * K₂
def R₀ : ℕ := 2 ^ 20000
def explicitUniversalConstant : ℕ := 200 * R₀ + 8196 * K₀

end Problem56
