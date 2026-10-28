import OAI.ArithmeticGeometry.Descent.CMVariety.FixedSmoothLevelRigidity

/-! # Concrete Fiber Level Rigidity -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.ConcreteFiberLevelRigidity.Abelian

noncomputable section

/-! Fixed-enhancement rigidity yields isomorphisms of the literal scheme fibers,
preserving every retained map and the full level on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Topology

theorem equivariance_through_presentations
    {C : Type*} [Category* C] {X X' Y Y' : C}
    (e : X ≅ X') (d : Y ≅ Y') (u : X' ≅ Y') (a : X ⟶ X) (b : Y ⟶ Y)
    (h : (e.inv ≫ a ≫ e.hom) ≫ u.hom = u.hom ≫ d.inv ≫ b ≫ d.hom) :
    a ≫ (e.hom ≫ u.hom ≫ d.inv) = (e.hom ≫ u.hom ≫ d.inv) ≫ b := by
  apply (cancel_epi e.inv).mp
  apply (cancel_mono d.hom).mp
  simpa only [Category.assoc, e.inv_hom_id_assoc, d.inv_hom_id, Category.comp_id] using h

namespace FamilyPoints

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ}

def ActualEquivariantLevelFiberIso (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)
    {n r : ℕ} (level : G.FullLevel n) (k : Fin r → (G.scheme ⟶ G.scheme))
    (s₀ s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) : Prop :=
  ∃ e : (G.pullback s₀.left).scheme ≅ (G.pullback s.left).scheme,
    IsMonHom e.hom ∧
    (∀ i, FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G (k i) s₀ ≫ e.hom = e.hom ≫ FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G (k i) s) ∧
    ∀ (T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
      (a : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod n))),
      ((level.pullback s₀.left).hom.app (.op T) a).val ≫ e.hom =
        ((level.pullback s.left).hom.app (.op T) a).val

theorem actual_fiber_iso_of_presented_equivariant_level_iso
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)
    (present : ∀ s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback s.left))
    {n r : ℕ} (level : G.FullLevel n) (s₀ s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (m : Fin r → ((present s₀).variety.toOver ⟶ (present s₀).variety.toOver))
    (k : Fin r → (G.scheme ⟶ G.scheme))
    (hk₀ : ∀ i, (present s₀).comparison.inv ≫ FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G (k i) s₀ ≫
      (present s₀).comparison.hom = m i)
    (h : IntrinsicBaseLevelRigidity.Abelian.FamilyPoints.PresentedEquivariantLevelFiberIso G present level s₀ m k s) :
    ActualEquivariantLevelFiberIso G level k s₀ s := by
  obtain ⟨e, he, hmaps, hlevel⟩ := h
  let : IsMonHom e.hom := he
  refine ⟨StandardModuli.Abelian.ComplexAbelianPresentation.fiberIso (present s₀) (present s) e,
    StandardModuli.Abelian.ComplexAbelianPresentation.fiberIso_group (present s₀) (present s) e, ?_, hlevel⟩
  intro i
  apply equivariance_through_presentations (present s₀).comparison (present s).comparison e
    (FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G (k i) s₀) (FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G (k i) s)
  rw [hk₀ i]
  exact hmaps i

theorem smooth_fixed_tuple_locally_isomorphic_with_level [Smooth S.hom]
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)
    (present : ∀ s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback s.left))
    (n : ℕ) (hn : 0 < n) (level : G.FullLevel n) (s₀ : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (E : AlgebraicEnhancement.Abelian.CMEnhancement (present s₀).variety)
    (k : Fin E.size → (G.scheme ⟶ G.scheme)) (hk : ∀ i, IsMonHom (k i))
    (hk₀ : ∀ i, (present s₀).comparison.inv ≫ FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G (k i) s₀ ≫
      (present s₀).comparison.hom = E.map i) :
    ∀ᶠ s in 𝓝 s₀, ActualEquivariantLevelFiberIso G level k s₀ s := by
  have h := FixedSmoothLevelRigidity.Abelian.FamilyPoints.smooth_base_family_rigid_for_cm_enhancements_with_level G present n hn level s₀ E k hk hk₀
  exact h.mono (fun s hs => actual_fiber_iso_of_presented_equivariant_level_iso
    G present level s₀ s E.map k hk₀ hs)

end FamilyPoints

end

end OAI.ArithmeticGeometry.Descent.CMVariety.ConcreteFiberLevelRigidity.Abelian
