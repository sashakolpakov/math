import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.UnitCover
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.CechSections
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.SiteValues
import OAI.AlgebraicGeometry.FormalGeometry.Completion.DescentSectionsTo

/-! # Sheaf Descent -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.SheafDescent.Construction

noncomputable section

/-!
# Completion: the section-descent equalizer for actual pro-étale sheaves

The geometric cover and its computed overlap prove the section-descent
bijection used to identify descended algebra representatives.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u w

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (hf : WeaklyEtale (Spec.map (CommRingCat.ofHom f))) (hflat : f.FaithfullyFlat)
  (F : Sheaf (Scheme.ProEt.topology (Spec (CommRingCat.of R))) (Type w))
  (A : ProEtale.Algebras.Construction.ProEtaleAlgebra R)

include hflat

/-- Compatible local sections of an actual sheaf descend uniquely across the affine unit cover. -/
theorem proEtaleAffineSections_descend
    (s : DescentSectionsTo.Construction.DescentSections (ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf) (SiteValues.Construction.proEtaleAffineValues F.obj) A) :
    ∃! t : (SiteValues.Construction.proEtaleAffineValues F.obj).obj A,
      (SiteValues.Construction.proEtaleAffineValues F.obj).map ((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf).unit.app A) t = s.val := by
  have := UnitCover.Construction.proEtaleUnit_surjective f hf A hflat
  have := UnitCover.Construction.proEtaleUnit_quasiCompact f hf A
  exact ProEtale.CechSections.Construction.proEtaleSheaf_descend_section_of_isPullback F
    ((ProEtale.Algebras.Construction.proEtaleAlgebraSpec R).map ((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf).unit.app A).op)
    ((ProEtale.Algebras.Construction.proEtaleAlgebraSpec R).map ((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf).unit.app
      ((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraRestrict f hf).obj ((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraExtend f).obj A))).op)
    ((ProEtale.Algebras.Construction.proEtaleAlgebraSpec R).map ((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraRestrict f hf).map
      ((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraExtend f).map ((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf).unit.app A))).op)
    (UnitCover.Construction.proEtaleCech_isPullback f hf A) s.val s.property

/-- The actual sheaf condition supplies the required section-descent bijection. -/
theorem proEtaleAffineSectionToDescent_bijective :
    Function.Bijective
      (DescentSectionsTo.Construction.sectionToDescent (ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf) (SiteValues.Construction.proEtaleAffineValues F.obj) A) := by
  constructor
  · intro x y h
    have hh := congrArg Subtype.val h
    obtain ⟨t, _, ht⟩ := proEtaleAffineSections_descend f hf hflat F A
      (DescentSectionsTo.Construction.sectionToDescent (ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf) (SiteValues.Construction.proEtaleAffineValues F.obj) A x)
    exact (ht x rfl).trans (ht y hh.symm).symm
  · intro s
    obtain ⟨t, ht, _⟩ := proEtaleAffineSections_descend f hf hflat F A s
    exact ⟨t, Subtype.ext ht⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.SheafDescent.Construction
