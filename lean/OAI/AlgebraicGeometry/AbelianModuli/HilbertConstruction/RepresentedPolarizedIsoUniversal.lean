import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.LevelIsoFunctor

/-! # Represented Polarized Iso Universal -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RepresentedPolarizedIsoUniversal

noncomputable section

/-! An actual representation of the complete isomorphism functor carries a universal polarized full-level isomorphism, with a unique classifying morphism for every test. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (M : Over S)
variable (e : Family.LevelIsoFunctor.familyLevelIsoFunctor A B ≅ yoneda.obj M)

def representedUniversalLevelIso : Moduli.Isomorphisms.LevelPreservingIso (A.pullback M.hom) (B.pullback M.hom) :=
  e.inv.app (.op M) (𝟙 M)

theorem representedUniversalLevelIso_specialization (T : Over S) (c : T ⟶ M) :
    Moduli.Isomorphisms.LevelPreservingIso.atParameterPoint A B c (representedUniversalLevelIso A B M e) =
      e.inv.app (.op T) c := by
  have h := NatTrans.naturality_apply e.inv c.op (𝟙 M)
  change e.inv.app (.op T) (c ≫ 𝟙 M) =
    Moduli.Isomorphisms.LevelPreservingIso.atParameterPoint A B c (representedUniversalLevelIso A B M e) at h
  rw [Category.comp_id] at h
  exact h.symm

theorem representedUniversalLevelIso_existsUnique (T : Over S)
    (a : Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (B.pullback T.hom)) :
    ∃! c : T ⟶ M,
      Moduli.Isomorphisms.LevelPreservingIso.atParameterPoint A B c (representedUniversalLevelIso A B M e) = a := by
  have ha : e.inv.app (.op T) (e.hom.app (.op T) a) = a :=
    ConcreteCategory.congr_hom (e.hom_inv_id_app (.op T)) a
  refine ⟨e.hom.app (.op T) a, ?_, ?_⟩
  · exact (representedUniversalLevelIso_specialization A B M e T _).trans ha
  · intro c hc
    apply (ConcreteCategory.bijective_of_isIso (e.inv.app (.op T))).injective
    exact (representedUniversalLevelIso_specialization A B M e T c).symm.trans
      (hc.trans ha.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RepresentedPolarizedIsoUniversal
