import OAI.NumberTheory.PadicHodge.IntegralComparison.SplitExteriorAdjunction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ConormalRank

/-! # Conormal Adjunction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ConormalAdjunction

noncomputable section

/-! The determinant adjunction for the actual conormal sequence of a
smooth quotient. Changing the conormal basis has its exact determinant
factor; the quotient basis is auxiliary. -/

open _root_.Module
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

universe u v w t

section Linear

variable {A : Type u} [CommRing A]
  {U : Type v} [AddCommGroup U] [Module A U]
  {W : Type w} [AddCommGroup W] [Module A W]
  {V : Type t} [AddCommGroup V] [Module A V]
  {c g : ℕ} (bU bU' : Basis (Fin c) A U) (bW : Basis (Fin g) A W)
  (e : (U × W) ≃ₗ[A] V)

open OAI.NumberTheory.PadicHodge.IntegralComparison.SplitExteriorAdjunction OAI.NumberTheory.PadicHodge.IntegralComparison.TopExteriorCoordinates

theorem residue_conormal_basis :
    (SplitExteriorAdjunction.residue bU bW e).toLinearMap =
      bU.det bU' • (SplitExteriorAdjunction.residue bU' bW e).toLinearMap := by
  let b := SplitExteriorAdjunction.productBasis bU' bW e
  have hv : SplitExteriorAdjunction.residue bU bW e (TopExteriorCoordinates.generator b) = bU.det bU' • SplitExteriorAdjunction.residue bU' bW e (TopExteriorCoordinates.generator b) := by
    rw [SplitExteriorAdjunction.residue_generator, SplitExteriorAdjunction.residue_apply, TopExteriorCoordinates.generator, TopExteriorCoordinates.coordinate_wedge,
      SplitExteriorAdjunction.productBasis_det, Basis.det_self, mul_one]
  apply LinearMap.ext
  intro x
  change SplitExteriorAdjunction.residue bU bW e x = bU.det bU' • SplitExteriorAdjunction.residue bU' bW e x
  calc
    SplitExteriorAdjunction.residue bU bW e x = SplitExteriorAdjunction.residue bU bW e (TopExteriorCoordinates.coordinate b x • TopExteriorCoordinates.generator b) :=
      congrArg (SplitExteriorAdjunction.residue bU bW e) (TopExteriorCoordinates.reconstruct b x).symm
    _ = TopExteriorCoordinates.coordinate b x • (bU.det bU' • SplitExteriorAdjunction.residue bU' bW e (TopExteriorCoordinates.generator b)) := by
      rw [map_smul, hv]
    _ = bU.det bU' • SplitExteriorAdjunction.residue bU' bW e x := by
      rw [smul_comm, ← map_smul, TopExteriorCoordinates.reconstruct]

end Linear

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
  [Algebra.Smooth k R] (I : Ideal R) [Algebra.Smooth k (R ⧸ I)]
  {c g : ℕ} (bI : Basis (Fin c) (R ⧸ I) I.Cotangent)
  (bQ : Basis (Fin g) (R ⧸ I) Ω[R ⧸ I⁄k])

abbrev presentation := Algebra.Extension.ofSurjective (Ideal.Quotient.mkₐ k I) Ideal.Quotient.mk_surjective

def equivalence :
    (⋀[R ⧸ I]^(c + g) ((R ⧸ I) ⊗[R] Ω[R⁄k])) ≃ₗ[R ⧸ I] ⋀[R ⧸ I]^g Ω[R ⧸ I⁄k] := by
  letI : Algebra.Smooth k (presentation (k := k) I).Ring := inferInstanceAs (Algebra.Smooth k R)
  exact SplitExteriorAdjunction.residue
    (bI.map (AlgebraicGeometry.Resolution.Blowups.Quotient.ConormalProjective.Construction.quotientExtensionCotangentEquiv (k := k) I).symm) bQ
    (IntegralComparison.Smooth.ConormalRank.differentialSplit (presentation (k := k) I)).symm

theorem independent_quotient_basis (bQ' : Basis (Fin g) (R ⧸ I) Ω[R ⧸ I⁄k]) :
    equivalence I bI bQ = equivalence I bI bQ' := by
  let : Algebra.Smooth k (presentation (k := k) I).Ring := inferInstanceAs (Algebra.Smooth k R)
  exact SplitExteriorAdjunction.residue_independent_quotient_basis _ _ _ _

theorem conormal_basis (bI' : Basis (Fin c) (R ⧸ I) I.Cotangent) :
    (equivalence I bI bQ).toLinearMap =
      bI.det bI' • (equivalence I bI' bQ).toLinearMap := by
  let : Algebra.Smooth k (presentation (k := k) I).Ring := inferInstanceAs (Algebra.Smooth k R)
  have h := residue_conormal_basis
    (bI.map (AlgebraicGeometry.Resolution.Blowups.Quotient.ConormalProjective.Construction.quotientExtensionCotangentEquiv (k := k) I).symm)
    (bI'.map (AlgebraicGeometry.Resolution.Blowups.Quotient.ConormalProjective.Construction.quotientExtensionCotangentEquiv (k := k) I).symm) bQ
    (IntegralComparison.Smooth.ConormalRank.differentialSplit (presentation (k := k) I)).symm
  apply LinearMap.ext
  intro x
  simpa only [equivalence, LinearMap.smul_apply, LinearEquiv.coe_coe,
    Basis.det_map, Basis.map_apply, LinearEquiv.symm_symm,
    Function.comp_def, LinearEquiv.apply_symm_apply] using LinearMap.congr_fun h x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ConormalAdjunction
