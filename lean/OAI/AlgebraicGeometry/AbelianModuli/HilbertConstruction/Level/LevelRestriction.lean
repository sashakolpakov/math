import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Scheme
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionFunctoriality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms

/-! # Level Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The action of level-preserving isomorphisms on the geometric torsion subgroup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {g N : ℕ} {δ : Fin g → ℕ} {S : Scheme.{u}}
variable {A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S}

/-- A level-preserving isomorphism commutes with the two geometric level trivializations. -/
theorem Moduli.Isomorphisms.LevelPreservingIso.torsion_trivialization (e : Moduli.Isomorphisms.LevelPreservingIso A B) :
    A.level.schemeIso.hom ≫ Abelian.Schemes.AbelianScheme.torsionMap N e.abelian.hom =
      B.level.schemeIso.hom := by
  apply (cancel_mono (B.abelian.torsionInclusion N)).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => A.level.schemeIso.hom ≫ a)
      (Abelian.Schemes.AbelianScheme.torsionMap_comp_inclusion N e.abelian.hom)).trans
      (((Category.assoc _ _ _).symm.trans
        (congrArg (fun a => a ≫ e.abelian.hom) A.level.schemeIso_hom_basis)).trans
        ((e.level (Level.Scheme.constantFullLevelScheme g N S)
          ((Level.Scheme.constantFullLevelRepresentable g N S).homEquiv (𝟙 _))).trans
          B.level.schemeIso_hom_basis.symm)))

/-- A level-preserving automorphism acts as the identity on the actual torsion scheme. -/
theorem Moduli.Isomorphisms.LevelPreservingIso.torsion_automorphism_eq_id (e : Moduli.Isomorphisms.LevelPreservingIso A A) :
    Abelian.Schemes.AbelianScheme.torsionMap N e.abelian.hom = 𝟙 (A.abelian.torsionScheme N) := by
  apply (cancel_epi A.level.schemeIso.hom).mp
  exact e.torsion_trivialization.trans (Category.comp_id _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
