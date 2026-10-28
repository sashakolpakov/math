import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismFiberEquations
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothEquationLocus

/-! # Automorphism Equation Criterion -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismEquationCriterion

noncomputable section

section

/-! The actual polarization and full-level equations cut out a reduced
closed locus for a given group automorphism and its compatible inverse
dual. Its universal point is an actual polarized full-level automorphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem exists_reduced_fixed_polarized_automorphism_locus
    {S : Scheme.{0}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (e : A.abelian.scheme ≅ A.abelian.scheme) [IsMonHom e.hom]
    (d : A.dual.abelian.scheme ≅ A.dual.abelian.scheme) [IsMonHom d.hom]
    (hP : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d.hom ⊗ₘ e.hom).left A.dual.poincare.classOf = A.dual.poincare.classOf) :
    ∃ Z : Over S, IsReduced Z.left ∧ IsClosedImmersion Z.hom ∧
      ∃ u : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback Z.hom) (A.pullback Z.hom),
        u.abelian = (Over.pullback Z.hom).mapIso e ∧
        u.dual = (Over.pullback Z.hom).mapIso d ∧
        ∀ (T : Over S) [IsReduced T.left],
          ((Over.pullback T.hom).map (A.polarization.isogeny.hom ≫ d.hom) =
              (Over.pullback T.hom).map (e.hom ≫ A.polarization.isogeny.hom) ∧
            (Over.pullback T.hom).map (A.abelian.torsionInclusion N ≫ e.hom) =
              (Over.pullback T.hom).map (A.abelian.torsionInclusion N)) ↔
                ∃! _f : T ⟶ Z, True := by
  have : Etale (A.abelian.torsionScheme N).hom := A.level.torsion_etale
  obtain ⟨Z, hr, hc, hU, hclass⟩ := SmoothEquationLocus.exists_reduced_two_smooth_equation_locus
    (A.polarization.isogeny.hom ≫ d.hom) (e.hom ≫ A.polarization.isogeny.hom)
    (A.abelian.torsionInclusion N ≫ e.hom) (A.abelian.torsionInclusion N)
  exact ⟨Z, hr, hc, AutomorphismFiberEquations.polarizedAutomorphismOnFiber A e d hP Z.hom hU.1 hU.2, rfl, rfl, hclass⟩

end

/-! The fixed equations are necessary as well as sufficient for the
pulled-back group automorphism to preserve polarization and full level.
The inverse dual is forced by the actual Poincare identity. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem inverse_dual_eq_of_poincare
    {S : Scheme.{0}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    (e : A.scheme ≅ A.scheme) [IsMonHom e.hom]
    (d : D.abelian.scheme ⟶ D.abelian.scheme)
    (hP : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d ⊗ₘ e.hom).left D.poincare.classOf = D.poincare.classOf) :
    d = Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback D D e.inv := by
  apply DualFamilyMorphism.eq_dualPicardPullback_of_poincare D D e.inv
  have h := congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 D.abelian.scheme ⊗ₘ e.inv).left) hP
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← Over.comp_left] at h
  simpa only [tensorHom_comp_tensorHom, Category.id_comp, Iso.inv_hom_id] using h

theorem fixed_polarized_automorphism_equations_of_iso
    {S T : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (e : A.abelian.scheme ≅ A.abelian.scheme) [IsMonHom e.hom]
    (d : A.dual.abelian.scheme ≅ A.dual.abelian.scheme) [IsMonHom d.hom]
    (hP : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d.hom ⊗ₘ e.hom).left A.dual.poincare.classOf = A.dual.poincare.classOf)
    (f : T ⟶ S) (u : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback f) (A.pullback f))
    (hu : u.abelian = (Over.pullback f).mapIso e) :
    (Over.pullback f).map (A.polarization.isogeny.hom ≫ d.hom) =
        (Over.pullback f).map (e.hom ≫ A.polarization.isogeny.hom) ∧
      (Over.pullback f).map (A.abelian.torsionInclusion N ≫ e.hom) =
        (Over.pullback f).map (A.abelian.torsionInclusion N) := by
  have hdP : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback f).map d.hom ⊗ₘ u.abelian.hom).left
      (A.pullback f).dual.poincare.classOf = (A.pullback f).dual.poincare.classOf := by
    rw [hu]
    exact (AbelianModuli.ReferenceFamily.RosatiBaseChange.poincareEndomorphism_baseChange A.dual d.hom e.hom f).trans
      (congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.dual.poincarePullbackOverMap f).left) hP)
  have hd : (Over.pullback f).map d.hom = u.dual.hom :=
    (inverse_dual_eq_of_poincare (A.pullback f).dual u.abelian _ hdP).trans
      (AutomorphismEquations.polarizedAutomorphism_dual_eq (A.pullback f) u).symm
  constructor
  · rw [Functor.map_comp, Functor.map_comp, hd]
    have hp := u.polarization
    rw [hu] at hp
    exact hp
  · apply (TorsionFixingBaseChange.fixes_torsion_baseChange_iff A.abelian f N e.hom).mpr
    have hl := AutomorphismEquations.polarizedAutomorphism_torsion_inclusion (A.pullback f) u
    rw [hu] at hl
    exact hl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismEquationCriterion
