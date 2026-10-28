import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MonomialBoundaryAtlas
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialIdealSheaf
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RefinementHelpers
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Empty Boundary Atlas -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Smooth complex schemes carry the empty labelled boundary atlas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem EmptyBoundaryAtlas.Construction.hasEtaleBoundaryCharts_empty_of_smooth
    (k : Type u) [Field k] (R : CommRingCat.{u}) [Algebra k R] [Algebra.Smooth k R]
    {β : Type v} [IsEmpty β] (w : β → R) : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R w := by
  classical
  intro p
  let : p.asIdeal.IsPrime := p.isPrime
  obtain ⟨s, hs, r, pAlg, htor, het⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := p.asIdeal)
  let S := Localization.Away s
  let : Algebra (MvPolynomial (Fin r) k) S := pAlg
  let : IsScalarTower k (MvPolynomial (Fin r) k) S := htor
  let : Algebra.IsStandardEtale (MvPolynomial (Fin r) k) S := het
  let P := MvPolynomial (Fin r) k
  let ε := MvPolynomial.renameEquiv k (Equiv.ulift : ULift.{u} (Fin r) ≃ Fin r)
  let φ := (algebraMap P S).comp ε.toRingHom
  have hφ : φ.Etale := RingHom.Etale.stableUnderComposition ε.toRingHom (algebraMap P S)
    (RingHom.Etale.of_bijective ε.bijective) (RingHom.etale_algebraMap.mpr inferInstance)
  have hφk (c : k) : φ (MvPolynomial.C c) = algebraMap k S c := by
    change algebraMap P S (MvPolynomial.rename (Equiv.ulift : ULift.{u} (Fin r) ≃ Fin r) (MvPolynomial.C c)) = _
    rw [MvPolynomial.rename_C]
    exact (IsScalarTower.algebraMap_apply k P S c).symm
  obtain ⟨q, hq⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime s p hs
  refine ⟨{
    carrier := .of S
    algebra := inferInstance
    map := IsScalarTower.toAlgHom k R S
    isOpenImmersion := IsOpenImmersion.of_isLocalization s
    point := q
    point_over := hq
    model := {
      indices := ULift.{u} (Fin r)
      finite := inferInstance
      decidableEq := inferInstance
      map := φ
      etale := hφ
      ground := hφk
      coordinate := isEmptyElim
      distinct := fun i => isEmptyElim i
      multiplier := isEmptyElim
      multiplierUnit := fun i => isEmptyElim i
      equation := fun i => isEmptyElim i } }⟩

def Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.empty
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] :
    Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f (fun i : Fin 0 => Fin.elim0 i) [Finset.univ] where
  indices := X.affineOpens
  opens := id
  cover := iSup_affineOpens_eq_top X
  equations := fun _ i => Fin.elim0 i
  component := fun _ i => Fin.elim0 i
  boundary := fun U => by
    let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    let : Algebra.Smooth ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra_smooth f U
    exact EmptyBoundaryAtlas.Construction.hasEtaleBoundaryCharts_empty_of_smooth ℂ (.of Γ(X, U)) (fun i : Fin 0 => Fin.elim0 i)
  faces := fun _ => Boundary.Schedule.Construction.boundaryFacesCover_univ _

end

end OAI.AlgebraicGeometry.Resolution.Blowups
