/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.Algebra.Homology.Notation
import OAI.Algebra.Homology.CoconeShortExactNaturality

/-! # Derived Category Cone Naturality -/

namespace OAI.Algebra.Homology.DerivedCategoryConeNaturality.CochainComplex.mappingCocone

noncomputable section

open _root_.CochainComplex

/-!
# Naturality of the canonical short-exact-sequence cone comparison

-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open _root_.CochainComplex.mappingCocone

variable {C : Type*} [Category* C] [Abelian C]
  {S T : ShortComplex (CochainComplex C ℤ)}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The explicit shifted fiber lift is natural for short-complex
maps, before passing to any derived or homotopy category. -/
@[reassoc]
lemma shiftedLiftShortComplex_naturality (f : S ⟶ T) :
    f.τ₁⟦(1 : ℤ)⟧' ≫ MappingCoconeShortExact.CochainComplex.mappingCocone.shiftedLiftShortComplex T =
      MappingCoconeShortExact.CochainComplex.mappingCocone.shiftedLiftShortComplex S ≫
        mappingCone.map S.g T.g f.τ₂ f.τ₃ f.comm₂₃.symm := by
  ext n
  simp [MappingCoconeShortExact.CochainComplex.mappingCocone.shiftedLiftShortComplex, mappingCone.rotateHomotopyEquiv,
    mappingCone.map, mappingCone.lift_f _ _ _ _ n (n + 1) rfl,
    HomComplex.Cochain.leftShift, shiftFunctorObjXIso]
  simpa only [HomologicalComplex.comp_f, Category.assoc] using
    congrArg (fun g => g.f (n + 1) ≫ (mappingCone.inl T.g).v (n + 1) n (by omega))
      f.comm₁₂

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality on homology of the canonical cone comparison. -/
@[reassoc]
lemma shortExactHomologyIsoCone_naturality (f : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact) (n n' : ℤ) (h : 1 + n = n') :
    HomologicalComplex.homologyMap f.τ₁ n' ≫
      (CoconeShortExactNaturality.CochainComplex.mappingCocone.shortExactHomologyIsoCone T hT n n' h).hom =
    (CoconeShortExactNaturality.CochainComplex.mappingCocone.shortExactHomologyIsoCone S hS n n' h).hom ≫
      HomologicalComplex.homologyMap
        (mappingCone.map S.g T.g f.τ₂ f.τ₃ f.comm₂₃.symm) n := by
  let H := HomologicalComplex.homologyFunctor C ℤᵘᵖ 0
  change (H.shift n').map f.τ₁ ≫
      (((H.shiftIso 1 n n' h).inv.app T.X₁) ≫
        (H.shift n).map (MappingCoconeShortExact.CochainComplex.mappingCocone.shiftedLiftShortComplex T)) =
    ((H.shiftIso 1 n n' h).inv.app S.X₁ ≫
      (H.shift n).map (MappingCoconeShortExact.CochainComplex.mappingCocone.shiftedLiftShortComplex S)) ≫
      (H.shift n).map (mappingCone.map S.g T.g f.τ₂ f.τ₃ f.comm₂₃.symm)
  rw [(H.shiftIso 1 n n' h).inv.naturality_assoc f.τ₁,
    Functor.comp_map, ← Functor.map_comp, shiftedLiftShortComplex_naturality, Functor.map_comp,
    Category.assoc]

end

end OAI.Algebra.Homology.DerivedCategoryConeNaturality.CochainComplex.mappingCocone
