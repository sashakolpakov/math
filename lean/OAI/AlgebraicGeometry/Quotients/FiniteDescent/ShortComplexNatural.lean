import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechBoundary

/-! # Short Complex Natural -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ShortComplexNatural

noncomputable section

/-! Cohomology comparisons and joint boundary detection are unchanged by
a natural isomorphism between scalar functors. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

namespace Construction.ShortComplexNaturalIso

variable {R S : Type u} [CommRing R] [CommRing S]
variable {F G : ModuleCat.{u} R ⥤ ModuleCat.{u} S}
variable [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (e : F ≅ G)

include e

theorem naturality {C D : ShortComplex (ModuleCat.{u} R)} (a : C ⟶ D) :
    F.mapShortComplex.map a ≫ (D.mapNatIso e).hom =
      (C.mapNatIso e).hom ≫ G.mapShortComplex.map a := by
  apply ShortComplex.hom_ext
  · exact e.hom.naturality a.τ₁
  · exact e.hom.naturality a.τ₂
  · exact e.hom.naturality a.τ₃

theorem quasiIso {C D : ShortComplex (ModuleCat.{u} R)} (a : C ⟶ D)
    [ShortComplex.QuasiIso (F.mapShortComplex.map a)] :
    ShortComplex.QuasiIso (G.mapShortComplex.map a) :=
  ShortComplex.quasiIso_of_arrow_mk_iso (F.mapShortComplex.map a) (G.mapShortComplex.map a)
    (Arrow.isoMk (C.mapNatIso e) (D.mapNatIso e) (ShortComplexNaturalIso.naturality e a).symm)

theorem jointly {C T₁ T₂ : ShortComplex (ModuleCat.{u} R)} (r₁ : C ⟶ T₁) (r₂ : C ⟶ T₂)
    (hd : CechBoundary.Construction.CechBoundaryTransport.JointlyDetects (F.mapShortComplex.map r₁) (F.mapShortComplex.map r₂)) :
    CechBoundary.Construction.CechBoundaryTransport.JointlyDetects (G.mapShortComplex.map r₁) (G.mapShortComplex.map r₂) :=
  CechBoundary.Construction.CechBoundaryTransport.jointly_of_iso
    (G.mapShortComplex.map r₁) (G.mapShortComplex.map r₂)
    (F.mapShortComplex.map r₁) (F.mapShortComplex.map r₂)
    (C.mapNatIso e.symm) (T₁.mapNatIso e.symm).hom (T₂.mapNatIso e.symm).hom
    (ShortComplexNaturalIso.naturality e.symm r₁) (ShortComplexNaturalIso.naturality e.symm r₂) hd

end Construction.ShortComplexNaturalIso

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ShortComplexNatural
