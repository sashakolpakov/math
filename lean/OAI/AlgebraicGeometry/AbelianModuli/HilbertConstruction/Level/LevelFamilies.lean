import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Transport

/-! # Level Families -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Geometric restriction maps for families of full levels over a fixed abelian scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {g N : ℕ} {S : Scheme.{u}} {A : Abelian.Schemes.AbelianScheme g S}

/-- Restrict a level to a test scheme by geometric pullback and its canonical comparisons. -/
def Abelian.Schemes.AbelianScheme.FullLevel.restrict {T U : Over S} (level : (A.pullback U.hom).FullLevel N) (f : T ⟶ U) :
    (A.pullback T.hom).FullLevel N :=
  (((level.pullback f.left).transport (A.pullbackCompIso U.hom f.left).symm).transport
    (A.pullbackCongrIso (f.left ≫ U.hom) T.hom f.w))

/-- Restriction of a level pulled back from the base is its pullback to the new test scheme. -/
theorem Abelian.Schemes.AbelianScheme.FullLevel.restrict_pullback (base : A.FullLevel N) {T U : Over S} (f : T ⟶ U) :
    (base.pullback U.hom).restrict f = base.pullback T.hom := by
  change (((base.pullback U.hom).pullback f.left).transport
      (A.pullbackCompIso U.hom f.left).symm).transport
      (A.pullbackCongrIso (f.left ≫ U.hom) T.hom f.w) = _
  exact (congrArg (fun level => level.transport
    (A.pullbackCongrIso (f.left ≫ U.hom) T.hom f.w))
    (base.transport_pullbackComp U.hom f.left)).trans
      (base.transport_pullbackCongr (f.left ≫ U.hom) T.hom f.w)

/-- The labels of a geometrically restricted level are the restrictions of its labels. -/
theorem Abelian.Schemes.AbelianScheme.FullLevel.labelsEquiv_restrict [NeZero N] (base : A.FullLevel N) {T U : Over S}
    (level : (A.pullback U.hom).FullLevel N) (f : T ⟶ U) :
    (base.pullback T.hom).labelsEquiv (level.restrict f) =
      ((base.pullback U.hom).labelsEquiv level).comap ⟨f.left, f.left.continuous⟩ := by
  have hbase := base.restrict_pullback f
  have hlabels := Abelian.Schemes.AbelianScheme.FullLevel.labelsEquiv_transport
    (((base.pullback U.hom).pullback f.left).transport (A.pullbackCompIso U.hom f.left).symm)
    ((level.pullback f.left).transport (A.pullbackCompIso U.hom f.left).symm)
    (A.pullbackCongrIso (f.left ≫ U.hom) T.hom f.w)
  change ((base.pullback U.hom).restrict f).labelsEquiv (level.restrict f) = _ at hlabels
  rw [hbase] at hlabels
  exact hlabels.trans
    ((Abelian.Schemes.AbelianScheme.FullLevel.labelsEquiv_transport ((base.pullback U.hom).pullback f.left) (level.pullback f.left)
      (A.pullbackCompIso U.hom f.left).symm).trans
      (Abelian.Schemes.AbelianScheme.FullLevel.labelsEquiv_pullback (base.pullback U.hom) level f.left))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
