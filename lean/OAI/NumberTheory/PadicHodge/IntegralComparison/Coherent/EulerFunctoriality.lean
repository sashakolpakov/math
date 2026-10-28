import OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.EulerIndex
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechAllDegrees
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechPushforward

/-! # Euler Functoriality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.EulerFunctoriality.ProjectiveK

noncomputable section

/-! The coherent Euler index computes the genuine sheaf cohomology, so
it is independent of the projective embedding and respects affine
direct image over the specified coefficient field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechAllDegrees

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

def coherentCohomologyDimension {K : Type u} [Field K] {A : Scheme.{u}}
    (ρ : A ⟶ Spec (CommRingCat.of K)) (M : A.Modules) (q : ℕ) : ℕ :=
  letI := AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule ρ M q
  Module.finrank Γ(Spec (CommRingCat.of K), ⊤) (AlgebraicGeometry.SheafCohomology.AffineH.Projective.H M q)

theorem coherentCohomologyDimension_eq_cech
    {K : Type u} [Field K] {A : Scheme.{u}} [A.IsSeparated]
    (ρ : A ⟶ Spec (CommRingCat.of K)) (M : A.Modules) [M.IsQuasicoherent]
    {ι : Type u} [LinearOrder ι] (U : ι → A.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i)) (q : ℕ) :
    coherentCohomologyDimension ρ M q =
      Module.finrank Γ(Spec (CommRingCat.of K), ⊤)
        ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex ρ M U).homology q) := by
  let := AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule ρ M q
  exact (AlgebraicGeometry.SheafCohomology.Projective.BaseCechAllDegrees.orderedBaseCechHomologyAffineHLinearEquiv ρ M U hU hUaff q).finrank_eq.symm

variable {K : Type u} [Field K] {r : ℕ} {A : Scheme.{u}} [A.IsSeparated]
  (f : A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K))
  [IsClosedImmersion f]

theorem coherentEuler_eq_sum_native
    (ρ : A ⟶ Spec (CommRingCat.of K))
    (hf : f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ = ρ)
    (M : A.Modules) [M.IsQuasicoherent] (b : ℕ) (hb : r + 1 ≤ b) :
    EulerIndex.ProjectiveK.coherentEuler f M = ∑ q ∈ Finset.range b,
      (-1 : ℤ) ^ q * (coherentCohomologyDimension ρ M q : ℤ) := by
  subst ρ
  unfold EulerIndex.ProjectiveK.coherentEuler
  rw [AlgebraicGeometry.SheafCohomology.Projective.EulerRange.MvPolynomial.projectiveSheafEuler_eq_sum_range _ AlgebraicGeometry.FormalGeometry.Completion.Projective.Numerics.Construction.fieldSpec_sections_isField b hb]
  let V := AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := K) (σ := Fin (r + 1))
  have hV : IsOpenCover V :=
    IsOpenCover.mk (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top
      (R := K) (σ := Fin (r + 1)))
  apply Finset.sum_congr rfl
  intro q _
  rw [coherentCohomologyDimension_eq_cech _ M (fun i => f ⁻¹ᵁ V i)
    (hV.comap f.base.hom)
    (fun i => (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := K) i).preimage f)]
  exact congrArg (fun n : ℕ => (-1 : ℤ) ^ q * (n : ℤ))
    (HomologicalComplex.homologyMapIso
      (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechPushforward.Scheme.Modules.orderedBaseCechComplexPushforwardIso f
        AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ M V) q).toLinearEquiv.finrank_eq.symm

theorem coherentEuler_eq_of_embedding
    {s : ℕ} (g : A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (s + 1)) K))
    [IsClosedImmersion g] (ρ : A ⟶ Spec (CommRingCat.of K))
    (hf : f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ = ρ)
    (hg : g ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ = ρ)
    (M : A.Modules) [M.IsQuasicoherent] :
    EulerIndex.ProjectiveK.coherentEuler f M = EulerIndex.ProjectiveK.coherentEuler g M := by
  rw [coherentEuler_eq_sum_native f ρ hf M (r + s + 2) (by omega),
    coherentEuler_eq_sum_native g ρ hg M (r + s + 2) (by omega)]

include f in
theorem coherentCohomologyDimension_pushforward_of_affine
    (ρ : A ⟶ Spec (CommRingCat.of K))
    (g : A ⟶ A) [IsAffineHom g] (hg : g ≫ ρ = ρ)
    (M : A.Modules) [M.IsQuasicoherent] (q : ℕ) :
    coherentCohomologyDimension ρ ((Scheme.Modules.pushforward g).obj M) q =
      coherentCohomologyDimension ρ M q := by
  have : ((Scheme.Modules.pushforward g).obj M).IsQuasicoherent :=
    AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom g
  let U := fun i : ULift.{u} (Fin (r + 1)) =>
    f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := K) i
  have hU : IsOpenCover U :=
    (IsOpenCover.mk (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top
      (R := K) (σ := Fin (r + 1)))).comap f.base.hom
  have hUaff (i : ULift.{u} (Fin (r + 1))) : IsAffineOpen (U i) :=
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := K) i).preimage f
  rw [coherentCohomologyDimension_eq_cech ρ _ U hU hUaff q,
    coherentCohomologyDimension_eq_cech ρ M (fun i => g ⁻¹ᵁ U i)
      (hU.comap g.base.hom) (fun i => (hUaff i).preimage g) q]
  have he := (HomologicalComplex.homologyMapIso
    (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechPushforward.Scheme.Modules.orderedBaseCechComplexPushforwardIso g ρ M U) q).toLinearEquiv.finrank_eq
  rw [hg] at he
  exact he.symm

theorem coherentEuler_pushforward_of_affine
    (ρ : A ⟶ Spec (CommRingCat.of K))
    (hf : f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ = ρ)
    (g : A ⟶ A) [IsAffineHom g] (hg : g ≫ ρ = ρ)
    (M : A.Modules) [M.IsQuasicoherent] :
    EulerIndex.ProjectiveK.coherentEuler f ((Scheme.Modules.pushforward g).obj M) = EulerIndex.ProjectiveK.coherentEuler f M := by
  have : ((Scheme.Modules.pushforward g).obj M).IsQuasicoherent :=
    AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom g
  rw [coherentEuler_eq_sum_native f ρ hf _ (r + 1) le_rfl,
    coherentEuler_eq_sum_native f ρ hf M (r + 1) le_rfl]
  apply Finset.sum_congr rfl
  intro q _
  rw [coherentCohomologyDimension_pushforward_of_affine f ρ g hg M q]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.EulerFunctoriality.ProjectiveK
