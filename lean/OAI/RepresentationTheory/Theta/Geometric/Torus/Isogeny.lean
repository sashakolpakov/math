import OAI.RepresentationTheory.Theta.Geometric.Torus.Hom
import OAI.RepresentationTheory.Theta.Geometric.CMIsogenies

/-! # Isogeny -/

namespace OAI.RepresentationTheory.Theta.Geometric.Torus.Isogeny

noncomputable section

/-! Complementary integral maps of period lattices produce actual finite
etale isogenies between the algebraic abelian models. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsProper A.toOver.hom := A.variety.presentation.projective.isProper

theorem finite_etale_surjective_of_two_complements (A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f : A.toOver ⟶ B.toOver) (h : B.toOver ⟶ A.toOver)
    (n : ℕ) (hn : 0 < n) (hfh : f ≫ h = (𝟙 A.toOver) ^ n)
    (hhf : h ≫ f = (𝟙 B.toOver) ^ n) :
    IsFinite f.left ∧ Etale f.left ∧ Surjective f.left := by
  let : NeZero n := ⟨hn.ne'⟩
  have hAn : Etale (((𝟙 A.toOver) ^ n).left) := AlgebraicGeometry.AbelianScheme.TorsionQuotient.Etale.TorsionEtale.power_etale A.toOver n
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionEtaleAt.TorsionEtale.integer_unit_at_stalk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) n)
  have hBn : Etale (((𝟙 B.toOver) ^ n).left) := AlgebraicGeometry.AbelianScheme.TorsionQuotient.Etale.TorsionEtale.power_etale B.toOver n
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionEtaleAt.TorsionEtale.integer_unit_at_stalk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) n)
  have hfh' : f.left ≫ h.left = ((𝟙 A.toOver) ^ n).left := congrArg Over.Hom.left hfh
  have hhf' : h.left ≫ f.left = ((𝟙 B.toOver) ^ n).left := congrArg Over.Hom.left hhf
  have : Etale (f.left ≫ h.left) := by rw [hfh']; exact hAn
  have : Etale (h.left ≫ f.left) := by rw [hhf']; exact hBn
  have : LocallyOfFiniteType (h.left ≫ A.toOver.hom) := by rw [h.w]; infer_instance
  have : LocallyOfFiniteType h.left := locallyOfFiniteType_of_comp h.left A.toOver.hom
  have : FormallyUnramified h.left := FormallyUnramified.of_comp h.left f.left
  have : Etale f.left := Etale.of_comp f.left h.left
  have : IsProper (f.left ≫ B.toOver.hom) := by rw [f.w]; infer_instance
  have : IsProper f.left := IsProper.of_comp f.left B.toOver.hom
  refine ⟨AlgebraicGeometry.AbelianScheme.TorsionQuotient.Quasi.TorsionGeometry.finite_of_proper_formallyUnramified f.left, inferInstance, ?_⟩
  have hr : IsClopen (Set.range f.left) :=
    ⟨f.left.isClosedMap.isClosed_range, f.left.isOpenMap.isOpen_range⟩
  exact ⟨Set.range_eq_univ.mp (hr.eq_univ (Set.range_nonempty f.left))⟩

theorem torusLinearMap_comp_nsmul (Φ Ψ : Data.CM.ProjectivePeriodData)
    (f : Φ.space →ₗ[ℂ] Ψ.space) (h : Ψ.space →ₗ[ℂ] Φ.space)
    (hf : ∀ v, v ∈ Φ.periodIntegerLattice → f v ∈ Ψ.periodIntegerLattice)
    (hh : ∀ v, v ∈ Ψ.periodIntegerLattice → h v ∈ Φ.periodIntegerLattice)
    (n : ℕ) (hc : ∀ v, h (f v) = n • v) (t : Φ.periodTorus) :
    Torus.Hom.torusLinearMap Ψ Φ h hh (Torus.Hom.torusLinearMap Φ Ψ f hf t) = n • t := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective t
  change QuotientAddGroup.mk (h (f v)) = n • (QuotientAddGroup.mk v : Φ.periodTorus)
  rw [hc]
  exact map_nsmul (QuotientAddGroup.mk' Φ.periodIntegerLattice.toAddSubgroup) n v

theorem groupComparison_nsmul {T : Type} [AddCommGroup T] (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : T ≃ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) (he : ∀ u v, e (u + v) = e u * e v)
    (n : ℕ) (t : T) : e (n • t) = (e t) ^ n := by
  let a : T ≃+ AlgebraicAction.AbelianPoints A :=
    { toFun := fun t => Additive.ofMul (e t)
      invFun := fun p => e.symm p.toMul
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply
      map_add' := he }
  exact congrArg Additive.toMul (map_nsmul a n t)

theorem algebraic_torus_composition (Φ Ψ : Data.CM.ProjectivePeriodData)
    (f : Φ.space →ₗ[ℂ] Ψ.space) (h : Ψ.space →ₗ[ℂ] Φ.space)
    (hf : ∀ v, v ∈ Φ.periodIntegerLattice → f v ∈ Ψ.periodIntegerLattice)
    (hh : ∀ v, v ∈ Ψ.periodIntegerLattice → h v ∈ Φ.periodIntegerLattice)
    (n : ℕ) (hc : ∀ v, h (f v) = n • v) (A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (eA : Φ.periodTorus ≃ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (eB : Ψ.periodTorus ≃ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver)
    (hA : ∀ u v, eA (u + v) = eA u * eA v)
    (F : A.toOver ⟶ B.toOver) (H : B.toOver ⟶ A.toOver)
    (hF : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map F (eA t) = eB (Torus.Hom.torusLinearMap Φ Ψ f hf t))
    (hH : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map H (eB t) = eA (Torus.Hom.torusLinearMap Ψ Φ h hh t)) :
    F ≫ H = (𝟙 A.toOver) ^ n := by
  apply AlgebraicGeometry.Albanese.Construction.ClosedPoints.hom_ext_of_points
  intro p
  obtain ⟨t, rfl⟩ := eA.surjective p
  calc
    eA t ≫ (F ≫ H) = (eA t ≫ F) ≫ H := (Category.assoc _ _ _).symm
    _ = eB (Torus.Hom.torusLinearMap Φ Ψ f hf t) ≫ H := congrArg (fun p => p ≫ H) (hF t)
    _ = eA (Torus.Hom.torusLinearMap Ψ Φ h hh (Torus.Hom.torusLinearMap Φ Ψ f hf t)) := hH _
    _ = eA (n • t) := congrArg eA (torusLinearMap_comp_nsmul Φ Ψ f h hf hh n hc t)
    _ = (eA t) ^ n := groupComparison_nsmul A eA hA n t
    _ = eA t ≫ (𝟙 A.toOver) ^ n := by rw [MonObj.comp_pow, Category.comp_id]

theorem exists_algebraic_torus_isogeny (Φ Ψ : Data.CM.ProjectivePeriodData)
    (f : Φ.space →ₗ[ℂ] Ψ.space) (h : Ψ.space →ₗ[ℂ] Φ.space)
    (hf : ∀ v, v ∈ Φ.periodIntegerLattice → f v ∈ Ψ.periodIntegerLattice)
    (hh : ∀ v, v ∈ Ψ.periodIntegerLattice → h v ∈ Φ.periodIntegerLattice)
    (n : ℕ) (hn : 0 < n) (hc : ∀ v, h (f v) = n • v) (hd : ∀ v, f (h v) = n • v)
    (A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (eA : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (eB : Ψ.periodTorus ≃ₘ⟮𝓘(ℂ, Ψ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel B)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver)
    (hA : ∀ u v, eA (u + v) = eA u * eA v)
    (hB : ∀ u v, eB (u + v) = eB u * eB v) :
    ∃ F : A.toOver ⟶ B.toOver, IsMonHom F ∧ IsFinite F.left ∧ Etale F.left ∧ Surjective F.left ∧
      ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map F (eA t) = eB (Torus.Hom.torusLinearMap Φ Ψ f hf t) := by
  obtain ⟨F, hFg, hF⟩ := Torus.Hom.exists_algebraic_torus_map Φ Ψ f hf A B eA eB hA hB
  obtain ⟨H, _, hH⟩ := Torus.Hom.exists_algebraic_torus_map Ψ Φ h hh B A eB eA hB hA
  have hFH := algebraic_torus_composition Φ Ψ f h hf hh n hc A B eA.toEquiv eB.toEquiv hA F H hF hH
  have hHF := algebraic_torus_composition Ψ Φ h f hh hf n hd B A eB.toEquiv eA.toEquiv hB H F hH hF
  have hgeom := finite_etale_surjective_of_two_complements A B F H n hn hFH hHF
  exact ⟨F, hFg, hgeom.1, hgeom.2.1, hgeom.2.2, hF⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Torus.Isogeny
