import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FppfBaseCoverSieve
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SheafCoverIso

/-! # Sheaf Base Change Conservative -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.SheafBaseChangeConservative

noncomputable section

/-! Restriction through a surjective fppf base morphism detects
isomorphisms of sheaves on the big relative site. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u w
variable {S V : Scheme.{u}} (b : V ⟶ S)
    [Flat b] [Surjective b] [LocallyOfFinitePresentation b]
    {F G : Sheaf (Scheme.fppfTopology.over S) (Type w)}

theorem sheaf_isIso_of_fppf_baseChange (φ : F ⟶ G)
    [IsIso ((Scheme.fppfTopology.overMapPullback (Type w) b).map φ)] :
    IsIso φ := by
  apply SheafCoverIso.sheaf_isIso_of_cover_bijective φ
  intro T
  refine ⟨FppfBaseCoverSieve.baseLiftSieve b T, FppfBaseCoverSieve.baseLiftSieve_mem b T, ?_⟩
  rintro Y f ⟨a, ha⟩
  let Z : Over S := (Over.map b).obj (Over.mk a)
  let e : Z ≅ Y := Over.isoMk (Iso.refl _) (by simpa [Z] using ha.symm)
  have hz : IsIso (φ.hom.app (.op Z)) :=
    inferInstanceAs (IsIso
      (((Scheme.fppfTopology.overMapPullback (Type w) b).map φ).hom.app (.op (Over.mk a))))
  have he : φ.hom.app (.op Y) =
      F.obj.map e.hom.op ≫ φ.hom.app (.op Z) ≫ G.obj.map e.inv.op := by
    rw [← Category.assoc, φ.hom.naturality e.hom.op, Category.assoc, ← G.obj.map_comp]
    simp
  rw [← isIso_iff_bijective, he]
  infer_instance

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.SheafBaseChangeConservative
