import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.PushforwardInjective
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Additive Pushforward -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Closed.AdditivePushforward.Cech

noncomputable section

/-! Direct image along a closed embedding is exact for actual abelian sheaves, with its original stalk maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open _root_.TopCat.Presheaf

def additiveSheafStalk (X : TopCat.{0}) (x : X) :
    TopCat.Sheaf AddCommGrpCat.{0} X ⥤ AddCommGrpCat.{0} :=
  TopCat.Sheaf.forget AddCommGrpCat X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat x

instance additiveSheafStalk_additive (X : TopCat.{0}) (x : X) :
    (additiveSheafStalk X x).Additive := by
  constructor
  intro F G φ ψ
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (φ.hom + ψ.hom) =
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φ.hom +
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map ψ.hom
  exact (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map_add

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

theorem additivePushforwardStalk_naturality
    {F G : TopCat.Presheaf AddCommGrpCat.{0} X} (φ : F ⟶ G) (x : X) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat (f x)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat f).map φ) ≫
        G.stalkPushforward AddCommGrpCat f x =
      F.stalkPushforward AddCommGrpCat f x ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φ := by
  apply ((TopCat.Presheaf.pushforward AddCommGrpCat f).obj F).stalk_hom_ext
  intro U hx
  erw [← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ, Category.assoc,
    TopCat.Presheaf.stalkPushforward_germ, ← Category.assoc,
    TopCat.Presheaf.stalkPushforward_germ, TopCat.Presheaf.stalkFunctor_map_germ]
  rfl

def additivePushforwardStalkIso (hf : Topology.IsInducing f) (x : X) :
    TopCat.Sheaf.pushforward AddCommGrpCat f ⋙ additiveSheafStalk Y (f x) ≅
      additiveSheafStalk X x := by
  exact NatIso.ofComponents (fun F =>
    @asIso _ _ _ _ (TopCat.Presheaf.stalkPushforward AddCommGrpCat f F.obj x)
      (TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing AddCommGrpCat hf F.obj x))
    (fun φ => additivePushforwardStalk_naturality f φ.hom x)

theorem closedAdditivePushforwardStalkZero (hclosed : IsClosed (Set.range f))
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (y : Y) (hy : y ∉ Set.range f) :
    IsZero ((additiveSheafStalk Y y).obj ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F)) := by
  let P : TopCat.Presheaf AddCommGrpCat.{0} Y := ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F).obj
  let U : Opens Y := ⟨(Set.range f)ᶜ, hclosed.isOpen_compl⟩
  change IsZero (P.stalk y)
  rw [IsZero.iff_id_eq_zero]
  apply P.stalk_hom_ext
  intro V hyV
  simp only [Category.comp_id, comp_zero]
  have hempty : (Opens.map f).obj (V ⊓ U) = ⊥ := by
    ext x
    constructor
    · intro hx
      change f x ∈ V ∧ f x ∉ Set.range f at hx
      exact (hx.2 ⟨x, rfl⟩).elim
    · intro hx
      exact hx.elim
  have hz : IsZero (P.obj (op (V ⊓ U))) := (F.isTerminalOfEqEmpty hempty).isZero
  have hw : P.germ (V ⊓ U) y ⟨hyV, hy⟩ = 0 := hz.eq_of_src _ _
  have hr := P.germ_res (homOfLE inf_le_left : V ⊓ U ⟶ V) y ⟨hyV, hy⟩
  exact hr.symm.trans (by rw [hw, comp_zero])

theorem closedAdditivePushforward_map_exact (hf : Topology.IsInducing f)
    (hclosed : IsClosed (Set.range f))
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)) (hS : S.Exact) :
    (S.map (TopCat.Sheaf.pushforward AddCommGrpCat f)).Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).mpr
  intro y
  by_cases hy : y ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hy
    have hs : (S.map (additiveSheafStalk X x)).Exact :=
      (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).mp hS x
    exact (ShortComplex.exact_iff_of_iso
      (S.mapNatIso (additivePushforwardStalkIso f hf x))).mpr hs
  · exact ShortComplex.exact_of_isZero_X₂ _ (closedAdditivePushforwardStalkZero f hclosed S.X₂ y hy)

theorem closedAdditivePushforwardExact (hf : Topology.IsInducing f)
    (hclosed : IsClosed (Set.range f)) :
    PreservesFiniteLimits (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f) ∧
      PreservesFiniteColimits (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f) :=
  ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).exact_tfae.out 2 4).mp
    (closedAdditivePushforward_map_exact f hf hclosed)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Closed.AdditivePushforward.Cech
