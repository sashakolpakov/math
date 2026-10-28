import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.AffineOrbits
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.RelabelReduction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.ComparisonBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.PELId
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.FineBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.RigidityScalarChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.RigidityPullback

/-! # Specialized Reduced Orbits -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.SpecializedReducedOrbits

noncomputable section

/-! A specialized invariant affine cover gives affine auxiliary
orbits for the actual reduced fine PEL parameter, with its exact
coefficient embedding and prescribed rigidity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R R' : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [CommRing R'] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {j : NumberField.RingOfIntegers E →+* R'}
    {X : Over (Spec (.of R))} [IsReduced X.left]

theorem specialized_reduced_pel_affine_orbits
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine) (hrigid : U.PrescribedRigid)
    (φ : R →+* R') (hemb : φ.comp iotaO = j) {I : Type}
    (V : I → ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X).left.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) (hcover : iSup V = ⊤)
    (hInv : ∀ σ : AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L, ∀ i,
      ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).map (U.auxiliaryRelabelMap hU σ)).left ⁻¹ᵁ V i = V i) :
    let Y := (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X
    let A := ((U.baseChange φ).changeEmbedding hemb).pullback (Reduction.reductionι Y)
    ∃ hA : A.IsFine, A.PrescribedRigid ∧
      ∀ x : (Reduction.reduction Y).left, ∃ W : (Reduction.reduction Y).left.Opens, IsAffineOpen W ∧
        ∀ y, Quotients.FiniteDescent.Invariant.Construction.InvariantCore.Related (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source (Reduction.reduction Y) (3 * s) L).left
          (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target A hA).left x y → y ∈ W := by
  let Y := (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X
  let A₀ := (U.baseChange φ).changeEmbedding hemb
  let A := A₀.pullback (Reduction.reductionι Y)
  have hA₀ : A₀.IsFine := IntegralAdded.PELId.integralAddedPEL_fine_changeEmbedding (U.baseChange φ) hemb
    (IntegralAdded.FineBaseChange.integralAddedPEL_fine_baseChange U hU φ)
  have hA : A.IsFine := IntegralAdded.FineReduction.integralAddedPEL_fine_reduction A₀ hA₀
  have hr₀ : A₀.PrescribedRigid := IntegralPrescribed.RigidityScalarChange.integralAddedPEL_prescribedRigid_baseChange U hrigid φ
  let a := fun σ => (Over.pullback (Spec.map (CommRingCat.ofHom φ))).map (U.auxiliaryRelabelMap hU σ)
  obtain ⟨haff, hfull, hstable⟩ := Reduced.InvariantAffineCover.invariant_affine_cover_reduction Y a V hV hcover hInv
  have hmaps (σ : AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L) : Reduced.InvariantAffineCover.reducedEndomorphism (a σ) = A.auxiliaryRelabelMap hA σ := by
    let e := U.auxiliaryRelabelComparison_baseChange hU φ σ
    exact A₀.reduced_relabel_map_eq hA₀ σ (a σ) { auxiliary := e.auxiliary, prescribed := e.prescribed }
  refine ⟨hA, A₀.prescribedRigid_pullback hr₀ (Reduction.reductionι Y), ?_⟩
  apply IntegralAuxiliary.AffineOrbits.IntegralAuxiliaryAction.affine_orbits_of_relabel_cover A hA
    (fun i => (Reduction.reductionι Y).left ⁻¹ᵁ V i) haff hfull
  intro σ i
  rw [← hmaps]
  exact hstable σ i

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.SpecializedReducedOrbits
