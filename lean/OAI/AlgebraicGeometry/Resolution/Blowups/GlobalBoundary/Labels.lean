import OAI.AlgebraicGeometry.Resolution.Blowups.SupportedBoundaryCenterExtension
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.SequenceCompatibility
import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.PartialLabelTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.CanonicalBoundaryAtlas

/-! # Labels -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

section

/-! Native boundary and center atlases retain partially relabelled components and unit labels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.pullbackLabels
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {I : X.IdealSheafData}
    {β γ : Type} [Fintype γ] {D : β → X.IdealSheafData}
    (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D) (p : γ → Option β)
    (hp : ∀ i j s, p i = some s → p j = some s → i = j)
    (E : γ → X.IdealSheafData) (hE : ∀ j, E j = match p j with | none => ⊤ | some s => D s) :
    Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I E := by
  classical
  let v (i : A.indices) (j : γ) : Γ(X, A.opens i) :=
    match p j with | none => 1 | some s => A.equations i s
  let F (i : A.indices) := Finset.univ.filter (fun j => ∃ s ∈ A.divided i, p j = some s)
  refine { indices := A.indices
           opens := A.opens
           cover := A.cover
           equations := v
           divided := F
           component := ?_
           contained := ?_
           boundary := ?_
           center := ?_ }
  · intro i j
    rw [hE j]
    cases hj : p j with
    | none =>
        change (⊤ : Ideal Γ(X, A.opens i)) = Ideal.span {v i j}
        simp only [v, hj]
        exact Ideal.span_singleton_one.symm
    | some s =>
        change (D s).ideal (A.opens i) = Ideal.span {v i j}
        simpa only [v, hj] using A.component i s
  · intro i j hj
    obtain ⟨s, hs, hpj⟩ := (Finset.mem_filter.mp hj).2
    simpa only [v, hpj] using A.contained i s hs
  · intro i
    let : Algebra ℂ Γ(X, A.opens i) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens i)
    apply (A.boundary i).pullbackLabels p hp (v i) (fun _ => 1) (fun _ => isUnit_one)
    intro j
    exact (one_mul (v i j)).symm
  · intro i
    let : Algebra ℂ Γ(X, A.opens i) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens i)
    apply (A.center i).pullbackLabels p hp (v i) (fun _ => 1) (fun _ => isUnit_one)
      (fun j => (one_mul (v i j)).symm) (F i)
    intro j
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]

def Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.pullbackLabels
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {β γ : Type} [Fintype γ]
    {D : β → X.IdealSheafData} {L : List (Finset β)}
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D L) (p : γ → Option β)
    (hp : ∀ i j s, p i = some s → p j = some s → i = j)
    (E : γ → X.IdealSheafData) (hE : ∀ j, E j = match p j with | none => ⊤ | some s => D s) :
    Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f E [Finset.univ] :=
  (A.unitCenter.pullbackLabels p hp E hE).boundaryAtlas

end

section

/-! Actual global boundary-compatible sequences retain any injectively relabelled boundary family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def GlobalBoundary.Labels.Construction.swapFirstBoundaryLabels {β : Type} : Option (Option β) ≃ Option (Option β) where
  toFun
    | none => some none
    | some none => none
    | some (some j) => some (some j)
  invFun
    | none => some none
    | some none => none
    | some (some j) => some (some j)
  left_inv := by intro j; rcases j with _ | (_ | j) <;> rfl
  right_inv := by intro j; rcases j with _ | (_ | j) <;> rfl

theorem Global.MonomialSequence.Construction.SmoothFixedControlSequence.boundaryCompatible_reindex
    {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (T : Global.MonomialSequence.Construction.SmoothFixedControlSequence b X f J) :
    ∀ (β γ : Type) [Fintype β] [Fintype γ] (D : β → X.IdealSheafData),
      T.boundaryCompatible β D → ∀ e : γ ↪ β,
        T.boundaryCompatible γ (fun j => D (e j)) := by
  induction T with
  | terminal h =>
      intro β γ _ _ D hB e
      obtain ⟨A⟩ := hB
      refine ⟨A.pullbackLabels (fun j => some (e j)) ?_ (fun j => D (e j)) (fun _ => rfl)⟩
      intro i j s hi hj
      exact e.injective (Option.some_injective _ (hi.trans hj.symm))
  | @blowup X _ _ f J I hI hb hp hs hbl tail ih =>
      intro β γ _ _ D hB e
      change Nonempty (Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D) ∧
        tail.boundaryCompatible (Option β) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) at hB
      obtain ⟨A⟩ := hB.1
      change Nonempty (Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I (fun j => D (e j))) ∧
        tail.boundaryCompatible (Option γ) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI (fun j => D (e j)))
      refine ⟨⟨A.pullbackLabels (fun j => some (e j)) ?_ (fun j => D (e j)) (fun _ => rfl)⟩, ?_⟩
      · intro i j s hi hj
        exact e.injective (Option.some_injective _ (hi.trans hj.symm))
      · let e' : Option γ ↪ Option β := ⟨Option.map e, Option.map_injective e.injective⟩
        have h := ih (Option β) (Option γ) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) hB.2 e'
        convert h using 1
        funext j
        cases j <;> rfl

theorem GlobalBoundary.Labels.Construction.canonical_boundary_swap_contained_carrier
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (I H : X.IdealSheafData) (hI : I ≠ ⊥) {β : Type} (D : β → X.IdealSheafData)
    (j : Option (Option β)) :
    CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI
      (fun l : Option β => match l with | none => H | some s => D s) (GlobalBoundary.Labels.Construction.swapFirstBoundaryLabels j) =
    (match j with
      | none => GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1
      | some l => CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D l) := by
  rcases j with _ | (_ | j) <;> rfl

end

/-! Retain a distinguished carrier boundary alongside the exceptional labels of a coefficient lift. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.dropFirst
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {β : Type} [Fintype β]
    {D : Option β → X.IdealSheafData} {L : List (Finset (Option β))}
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D L) :
    Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f (fun j => D (some j)) [Finset.univ] :=
  A.pullbackLabels (fun j : β => some (some j))
    (by intro i j s hi hj; exact Option.some_injective β (Option.some_injective (Option β) (hi.trans hj.symm)))
    (fun j => D (some j)) (fun _ => rfl)

def Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.blowupBoundaryWithCarrier
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {I H : X.IdealSheafData} {β : Type} [Fintype β] {D : β → X.IdealSheafData}
    (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I (fun j : Option β => match j with | none => H | some l => D l))
    (hI : I ≠ ⊥) :
    Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (fun j : Option (Option β) => match j with
        | none => GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1
        | some l => CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D l) [Finset.univ] := by
  apply (A.blowupBoundary hI).pullbackLabels (fun j => some (GlobalBoundary.Labels.Construction.swapFirstBoundaryLabels j))
  · intro i j s hi hj
    exact GlobalBoundary.Labels.Construction.swapFirstBoundaryLabels.injective (Option.some_injective _ (hi.trans hj.symm))
  · intro j
    exact (GlobalBoundary.Labels.Construction.canonical_boundary_swap_contained_carrier I H hI D j).symm

theorem Global.MonomialSequence.Construction.SmoothFixedControlSequence.boundaryCompatible_carrier_to_canonical
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {I H : X.IdealSheafData} (hI : I ≠ ⊥) {β : Type} [Fintype β] (D : β → X.IdealSheafData)
    {b : ℕ} {J : (GlobalBlowup.Data.Construction.globalBlowup I hI).IdealSheafData}
    (T : Global.MonomialSequence.Construction.SmoothFixedControlSequence b (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) J)
    (hT : T.boundaryCompatible (Option (Option β))
      (fun j => match j with
        | none => GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1
        | some l => CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D l)) :
    T.boundaryCompatible (Option (Option β))
      (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI (fun j : Option β => match j with | none => H | some l => D l)) := by
  have h := T.boundaryCompatible_reindex (Option (Option β)) (Option (Option β)) _ hT
    GlobalBoundary.Labels.Construction.swapFirstBoundaryLabels.toEmbedding
  convert h using 1
  funext j
  rcases j with _ | (_ | j) <;> rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups
