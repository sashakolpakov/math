import OAI.Algebra.Homology.DerivedCategoryConeNaturality
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-! # Canonical Kernel Cone Functor -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalKernelConeFunctor

noncomputable section

/-! # Additive functors preserve the positive canonical kernel-to-cone lift -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical lift has its literal positive inclusion component. -/
theorem shiftedLiftShortComplex_f (S : ShortComplex (CochainComplex C ℤ)) (n : ℤ) :
    (OAI.Algebra.Homology.MappingCoconeShortExact.CochainComplex.mappingCocone.shiftedLiftShortComplex S).f n =
      S.f.f (n + 1) ≫ (CochainComplex.mappingCone.inl S.g).v (n + 1) n (by omega) := by
  simp [OAI.Algebra.Homology.MappingCoconeShortExact.CochainComplex.mappingCocone.shiftedLiftShortComplex,
    CochainComplex.mappingCone.rotateHomotopyEquiv, CochainComplex.mappingCone.map,
    CochainComplex.mappingCone.lift_f _ _ _ _ n (n + 1) rfl,
    CochainComplex.HomComplex.Cochain.leftShift, CochainComplex.shiftFunctorObjXIso]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An additive functor preserves that actual inclusion and its cone normalization. -/
theorem shiftedLiftShortComplex_map (S : ShortComplex (CochainComplex C ℤ))
    (F : C ⥤ D) [F.Additive] :
    (F.mapHomologicalComplex (.up ℤ)).map
        (OAI.Algebra.Homology.MappingCoconeShortExact.CochainComplex.mappingCocone.shiftedLiftShortComplex S) ≫
      (CochainComplex.mappingCone.mapHomologicalComplexIso S.g F).hom =
    ((F.mapHomologicalComplex (.up ℤ)).commShiftIso 1).hom.app S.X₁ ≫
      OAI.Algebra.Homology.MappingCoconeShortExact.CochainComplex.mappingCocone.shiftedLiftShortComplex
        (S.map (F.mapHomologicalComplex (.up ℤ))) := by
  ext n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    shiftedLiftShortComplex_f, Functor.map_comp]
  simp only [CochainComplex.mappingCone.mapHomologicalComplexIso,
    HomologicalComplex.Hom.isoOfComponents_hom_f,
    CochainComplex.mappingCone.mapHomologicalComplexXIso_eq S.g F n (n + 1) rfl,
    CochainComplex.mappingCone.mapHomologicalComplexXIso'_hom,
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
    Preadditive.comp_add, Category.assoc,
    ← Functor.map_comp_assoc, CochainComplex.mappingCone.inl_v_fst_v,
    CochainComplex.mappingCone.inl_v_snd_v, Functor.map_zero, zero_comp]

  change F.map (S.f.f (n + 1) ≫ 𝟙 _) ≫
      (CochainComplex.mappingCone.inl ((F.mapHomologicalComplex (.up ℤ)).map S.g)).v
        (n + 1) n (by omega) + F.map (S.f.f (n + 1)) ≫ 0 =
    𝟙 _ ≫ F.map (S.f.f (n + 1)) ≫
      (CochainComplex.mappingCone.inl ((F.mapHomologicalComplex (.up ℤ)).map S.g)).v
        (n + 1) n (by omega)
  simp only [Category.comp_id, comp_zero, add_zero, Category.id_comp]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalKernelConeFunctor
