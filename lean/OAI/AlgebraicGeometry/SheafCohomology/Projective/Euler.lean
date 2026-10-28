import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechFinite
import OAI.AlgebraicGeometry.SheafCohomology.Projective.HomologyEulerBoundary

/-! # Euler -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.Euler

noncomputable section

open _root_.MvPolynomial

/-! Euler characteristics of actual coherent modules on projective space. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry OAI.AlgebraicGeometry.SheafCohomology.Projective.HomologyEulerBoundary
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {r : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance projectiveEulerOverRightAdjoints (X : Type u) [TopologicalSpace X] :
    ∀ U : TopologicalSpace.Opens X,
      (sheafToPresheaf ((Opens.grothendieckTopology X).over U)
        AddCommGrpCat.{u}).IsRightAdjoint := fun _ => inferInstance

local instance projectiveEulerOverLocallyBijective (X : Type u) [TopologicalSpace X] :
    ∀ U : TopologicalSpace.Opens X,
      ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  fun _ => inferInstance

def projectiveSheafEuler (M : (Proj (homogeneousSubmodule (Fin (r + 1)) R)).Modules) : ℤ :=
  ∑ q ∈ Finset.range (r + 1), (-1 : ℤ) ^ q *
    (Module.finrank Γ(Spec (CommRingCat.of R), ⊤)
      ((OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (r + 1))) M
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (r + 1)))).homology q) : ℤ)

theorem projectiveSheafEuler_eq_of_iso
    {M N : (Proj (homogeneousSubmodule (Fin (r + 1)) R)).Modules} (e : M ≅ N) :
    projectiveSheafEuler M = projectiveSheafEuler N := by
  apply Finset.sum_congr rfl
  intro q _
  let F := OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor
    (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (r + 1)))
    (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (r + 1)))
  exact congrArg (fun n : ℕ => (-1 : ℤ) ^ q * (n : ℤ))
    (HomologicalComplex.homologyMapIso (F.mapIso e) q).toLinearEquiv.finrank_eq

theorem projectiveSheafEuler_add_of_shortExact [IsNoetherianRing R]
    (T : ShortComplex (Proj (homogeneousSubmodule (Fin (r + 1)) R)).Modules)
    (hT : T.ShortExact) (hfield : IsField Γ(Spec (CommRingCat.of R), ⊤))
    [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent] [T.X₃.IsQuasicoherent]
    [T.X₁.IsFiniteType] [T.X₂.IsFiniteType] [T.X₃.IsFiniteType] :
    projectiveSheafEuler T.X₂ = projectiveSheafEuler T.X₁ + projectiveSheafEuler T.X₃ := by
  let := hfield.toField
  let F := OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor
    (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (r + 1)))
    (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (r + 1)))
  have hfinite (M : (Proj (homogeneousSubmodule (Fin (r + 1)) R)).Modules)
      [M.IsQuasicoherent] [M.IsFiniteType] (q : ℕ) :
      Module.Finite Γ(Spec (CommRingCat.of R), ⊤) ((F.obj M).homology q) :=
    TwistCechFinite.MvPolynomial.finiteType_orderedBaseCechComplex_homology_module_finite M q
  let : ∀ q, Module.Finite Γ(Spec (CommRingCat.of R), ⊤) ((T.map F).X₁.homology q) :=
    hfinite T.X₁
  let : ∀ q, Module.Finite Γ(Spec (CommRingCat.of R), ⊤) ((T.map F).X₂.homology q) :=
    hfinite T.X₂
  let : ∀ q, Module.Finite Γ(Spec (CommRingCat.of R), ⊤) ((T.map F).X₃.homology q) :=
    hfinite T.X₃
  have hX : IsZero ((T.map F).X₁.X (r + 1)) :=
    OrderedBaseCech.Scheme.Modules.orderedBaseCechObject_isZero_of_card_le
      (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (r + 1))) T.X₁
      (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (r + 1))) (r + 1) (by simp)
  let : Subsingleton ((T.map F).X₁.homology (r + 1)) :=
    ModuleCat.subsingleton_of_isZero
      (ShortComplex.isZero_homology_of_isZero_X₂ ((T.map F).X₁.sc (r + 1)) hX)
  exact HomologyEulerBoundary.alternating_homology_sum_add_of_vanish
    (OrderedBaseCechExact.CategoryTheory.ShortComplex.ShortExact.map_orderedBaseCechComplexFunctor_of_affine_openCover
      (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (r + 1)))
      (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (r + 1)))
      (StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R)) hT) r

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.Euler
