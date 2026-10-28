import Mathlib.CategoryTheory.Abelian.LeftDerived

/-! # Derived Zero Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.DerivedZeroNaturality

noncomputable section

/-! The comparison from degree-zero left derived functors is natural
also in the additive functor being derived. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasProjectiveResolutions C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {F G : C ⥤ D} [F.Additive] [G.Additive]

theorem naturality (α : F ⟶ G) (X : C) :
    (NatTrans.leftDerived α 0).app X ≫ G.fromLeftDerivedZero.app X =
      F.fromLeftDerivedZero.app X ≫ α.app X := by
  let P := projectiveResolution X
  let K := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let L := (G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let φ : K ⟶ L := (NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex
  have hop : HomologicalComplex.opcyclesMap φ 0 ≫ P.fromLeftDerivedZero' G =
      P.fromLeftDerivedZero' F ≫ α.app X := by
    rw [← cancel_epi (K.pOpcycles 0), HomologicalComplex.p_opcyclesMap_assoc,
      ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero',
      ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero'_assoc]
    exact (α.naturality (P.π.f 0)).symm
  have hh : HomologicalComplex.homologyMap φ 0 ≫ L.homologyι 0 ≫ P.fromLeftDerivedZero' G =
      K.homologyι 0 ≫ P.fromLeftDerivedZero' F ≫ α.app X := by
    rw [HomologicalComplex.homologyι_naturality_assoc, hop]
  rw [P.leftDerived_app_eq, P.fromLeftDerivedZero_eq G, P.fromLeftDerivedZero_eq F]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change (P.isoLeftDerivedObj F 0).hom ≫ HomologicalComplex.homologyMap φ 0 ≫
      L.homologyι 0 ≫ P.fromLeftDerivedZero' G =
    (P.isoLeftDerivedObj F 0).hom ≫ K.homologyι 0 ≫ P.fromLeftDerivedZero' F ≫ α.app X
  exact congrArg (fun h => (P.isoLeftDerivedObj F 0).hom ≫ h) hh

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.DerivedZeroNaturality
