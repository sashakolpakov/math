import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.TransportComposition

/-! # Iso Conjugation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Group and ordered-level compatibility of the original conjugated
family isomorphism, established before specializing the families. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem Level.IsoConjugation.isoSymm_isMonHom {S : Scheme.{u}} {X Y : Over S}
    [MonObj X] [MonObj Y] (e : X ≅ Y) [hE : IsMonHom e.hom] :
    IsMonHom e.symm.hom :=
  inferInstanceAs (IsMonHom e.inv)

theorem Level.IsoConjugation.isoTrans_isMonHom {S : Scheme.{u}} {X Y Z : Over S}
    [MonObj X] [MonObj Y] [MonObj Z]
    (e : X ≅ Y) (f : Y ≅ Z) [hE : IsMonHom e.hom] [hF : IsMonHom f.hom] :
    IsMonHom (e ≪≫ f).hom :=
  inferInstanceAs (IsMonHom (e.hom ≫ f.hom))

theorem Level.IsoConjugation.isoConjugation_isMonHom {S : Scheme.{u}} {A B C D : Over S}
    [MonObj A] [MonObj B] [MonObj C] [MonObj D]
    (r : A ≅ B) (e : A ≅ C) (s : C ≅ D)
    [hR : IsMonHom r.hom] [hE : IsMonHom e.hom] [hS : IsMonHom s.hom] :
    IsMonHom (r.symm ≪≫ e ≪≫ s).hom :=
  inferInstanceAs (IsMonHom (r.inv ≫ e.hom ≫ s.hom))

theorem Abelian.Schemes.AbelianScheme.FullLevel.transport_conjugation {S : Scheme.{u}} {g N : ℕ}
    (A B C D : Abelian.Schemes.AbelianScheme g S)
    (r : A.scheme ≅ B.scheme) (e : A.scheme ≅ C.scheme) (s : C.scheme ≅ D.scheme)
    [hR : IsMonHom r.hom] [hE : IsMonHom e.hom] [hS : IsMonHom s.hom]
    (lA : A.FullLevel N) (lB : B.FullLevel N) (lC : C.FullLevel N) (lD : D.FullLevel N)
    (hr : lA.transport r = lB) (he : lA.transport e = lC) (hs : lC.transport s = lD) :
    letI : IsMonHom (r.symm ≪≫ e ≪≫ s).hom := Level.IsoConjugation.isoConjugation_isMonHom r e s
    lB.transport (r.symm ≪≫ e ≪≫ s) = lD := by
  let : IsMonHom r.symm.hom := Level.IsoConjugation.isoSymm_isMonHom r
  let : IsMonHom (r.symm ≪≫ e).hom := Level.IsoConjugation.isoTrans_isMonHom r.symm e
  let : IsMonHom (e ≪≫ s).hom := Level.IsoConjugation.isoTrans_isMonHom e s
  let : IsMonHom (r.symm ≪≫ e ≪≫ s).hom := Level.IsoConjugation.isoConjugation_isMonHom r e s
  have hleft : lB.transport r.symm = lA := ((Abelian.Schemes.AbelianScheme.FullLevel.transport_eq_iff r lA lB).mp hr).symm
  change lB.transport (r.symm ≪≫ e ≪≫ s) = lD
  rw [← Abelian.Schemes.AbelianScheme.FullLevel.transport_trans, ← Abelian.Schemes.AbelianScheme.FullLevel.transport_trans, hleft, he, hs]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
