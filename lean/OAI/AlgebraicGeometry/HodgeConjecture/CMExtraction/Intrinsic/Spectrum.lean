import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CharacterRefinement
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CentralFinite
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Base
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Commutativity

/-! # Spectrum -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Spectrum

noncomputable section

/-! The actual full Betti Hecke algebra refines GeometricTheta's actual active
operators. Every occurring active character extends to a full character,
and the entire active generalized eigenspace is the sum of these full
spaces. No full extension is supplied as a hypothesis. -/

open scoped TensorProduct

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Commutativity
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CharacterRefinement.Spectral

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

/-- The actual active algebra inclusion, with only its coefficients extended. -/
def nativeActiveHeckeInFull (F : Type*) [Field F] [Algebra ℚ F]
    (e : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished) :
    F ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q →ₐ[F] F ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q :=
  Algebra.TensorProduct.map (AlgHom.id F F)
    (RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.pel.reference.distinguished e)

def nativeActiveHeckeActionOver (F : Type*) [Field F] [Algebra ℚ F] (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel)
    (e : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished) :
    F ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q →ₐ[F] Module.End F (F ⊗[ℚ] D.pel.H1) :=
  (CentralFinite.nativeFullHeckeActionOver D.pel F A).comp (nativeActiveHeckeInFull D F e)

theorem nativeActiveHeckeActionOver_tmul (F : Type*) [Field F] [Algebra ℚ F]
    (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel)
    (e : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (c : F) (h : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    nativeActiveHeckeActionOver D F A e (c ⊗ₜ[ℚ] h) =
      c • (Forms.activeBettiAction D A e h).baseChange F := rfl

theorem nativeActiveHeckeActionOver_complex (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel)
    (e : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished) :
    (nativeActiveHeckeActionOver D ℂ A e).toLinearMap = D.activeH1Complex A e := by
  apply LinearMap.ext
  intro h
  induction h using TensorProduct.inductionOn with
  | tmul c h => rfl
  | add h k hh hk => simp only [map_add, hh, hk]

theorem native_full_character_refinement
    (hg : D.pel.HasIntegralModelGeometry) (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (F : Type*) [Field F] [Algebra ℚ F] [IsAlgClosed F]
    (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel)
    (e : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (χ : F ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q → F) :
    HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (nativeActiveHeckeActionOver D F A e) χ =
      ⨆ ψ : {ψ : F ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[F] F //
        ∀ h, ψ (nativeActiveHeckeInFull D F e h) = χ h},
        HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (CentralFinite.nativeFullHeckeActionOver D.pel F A) ψ.val := by
  let : FiniteDimensional ℚ D.pel.H1 := Base.native_betti_finite D hg
  let : CommRing (AbelianScheme.TateComparison.HeckeKernel.Hecke s q) :=
    { (inferInstance : Ring (AbelianScheme.TateComparison.HeckeKernel.Hecke s q)) with mul_comm := AbelianScheme.TateComparison.Commutativity.spherical_mul_comm s q hElementaryDivisors }
  exact CharacterRefinement.Spectral.jointSpace_full_character_refinement (CentralFinite.nativeFullHeckeActionOver D.pel F A)
    (nativeActiveHeckeInFull D F e) χ

theorem native_exists_occurring_full_character
    (hg : D.pel.HasIntegralModelGeometry) (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (F : Type*) [Field F] [Algebra ℚ F] [IsAlgClosed F]
    (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel)
    (e : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (χ : F ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q → F)
    (hχ : HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (nativeActiveHeckeActionOver D F A e) χ ≠ ⊥) :
    ∃ ψ : F ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[F] F,
      (∀ h, ψ (nativeActiveHeckeInFull D F e h) = χ h) ∧
      HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (CentralFinite.nativeFullHeckeActionOver D.pel F A) ψ ≠ ⊥ := by
  let : FiniteDimensional ℚ D.pel.H1 := Base.native_betti_finite D hg
  let : CommRing (AbelianScheme.TateComparison.HeckeKernel.Hecke s q) :=
    { (inferInstance : Ring (AbelianScheme.TateComparison.HeckeKernel.Hecke s q)) with mul_comm := AbelianScheme.TateComparison.Commutativity.spherical_mul_comm s q hElementaryDivisors }
  exact CharacterRefinement.Spectral.exists_occurring_full_character (CentralFinite.nativeFullHeckeActionOver D.pel F A)
    (nativeActiveHeckeInFull D F e) χ hχ

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Spectrum
