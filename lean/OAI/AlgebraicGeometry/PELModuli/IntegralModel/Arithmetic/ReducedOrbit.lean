import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.InvariantAffineCoverSpecialization
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.TowerEmbedding
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SpecializedReducedOrbits
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.Parameter

/-! # Reduced Orbit -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ReducedOrbit

noncomputable section

/-! Specialize an invariant complex cover and reduce the actual
base-changed two-level PEL parameter. The result is a fine arithmetic
parameter with its exact CM embedding, prescribed rigidity, and affine
neighborhoods of all auxiliary orbits. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {κ : K →+* ℂ} {s L N : ℕ} [NeZero L] [NeZero N]
    {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} (iota : E →+* K) (B : Base.ArithmeticBaseExtension K κ)
    [Algebra B.R ℂ] {X : Over B.base} [IsReduced X.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

theorem arithmetic_reduced_pel_affine_orbit_model
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P B.R (B.integralEmbedding iota) L N X)
    (hU : U.IsFine) (hrigid : U.PrescribedRigid)
    (hAlg : algebraMap B.R ℂ = B.embedding.comp B.toField) {I : Type} [Finite I]
    (V : I → ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B.R ℂ)))).obj X).left.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) (hcover : iSup V = ⊤)
    (hInv : ∀ σ : AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L, ∀ i,
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B.R ℂ)))).map
        (U.auxiliaryRelabelMap hU σ)).left ⁻¹ᵁ V i = V i) :
    ∃ C : Base.ArithmeticBaseExtension K κ, IsUnit (N : C.R) ∧ ∃ _φ : B.R →+* C.R,
      ∃ Z : Over C.base, ∃ hred : IsReduced Z.left, let _ : IsReduced Z.left := hred
        IsNoetherian Z.left ∧
        LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ IsSeparated Z.hom ∧
        ∃ A : IntegralAdded.PELId.IntegralAddedPELLevel P C.R (C.integralEmbedding iota) L N Z,
          ∃ hA : A.IsFine, A.PrescribedRigid ∧
            ∀ x : Z.left, ∃ W : Z.left.Opens, IsAffineOpen W ∧
              ∀ y, Quotients.FiniteDescent.Invariant.Construction.InvariantCore.Related (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source Z (3 * s) L).left
                (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target A hA).left x y → y ∈ W := by
  have hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom := ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨D, hdiv, φ, hφ, W, hW, hfull, hstable⟩ := InvariantAffineCoverSpecialization.arithmetic_invariant_affine_cover_specialization
    B hAlg X hX (fun σ => U.auxiliaryRelabelMap hU σ) V hV hcover hInv N (NeZero.ne N)
  let C := B.compose D
  let Y : Over C.base := (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X
  have hft : LocallyOfFiniteType Y.hom := inferInstanceAs
    (LocallyOfFiniteType (pullback.snd X.hom (Spec.map (CommRingCat.ofHom φ))))
  have hqc : QuasiCompact Y.hom := inferInstanceAs
    (QuasiCompact (pullback.snd X.hom (Spec.map (CommRingCat.ofHom φ))))
  have hsep : IsSeparated Y.hom := inferInstanceAs
    (IsSeparated (pullback.snd X.hom (Spec.map (CommRingCat.ofHom φ))))
  obtain ⟨hnZ, hftZ, hqcZ, hsepZ⟩ := Reduced.Parameter.reduced_parameter_geometry Y
  let hemb := B.compose_integralEmbedding D φ hφ iota
  let A := ((U.baseChange φ).changeEmbedding hemb).pullback (Reduction.reductionι Y)
  obtain ⟨hA, hrA, hOrbit⟩ := SpecializedReducedOrbits.specialized_reduced_pel_affine_orbits U hU hrigid φ hemb W hW hfull hstable
  exact ⟨C, C.divisor_isUnit N hdiv, φ, Reduction.reduction Y, inferInstance, hnZ, hftZ, hqcZ, hsepZ,
    A, hA, hrA, hOrbit⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ReducedOrbit
