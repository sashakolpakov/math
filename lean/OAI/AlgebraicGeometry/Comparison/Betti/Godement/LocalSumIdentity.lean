import OAI.AlgebraicGeometry.Comparison.Betti.Godement.Resolution
import OAI.AlgebraicGeometry.Comparison.Betti.Godement.SupportedExtension

/-! # Local Sum Identity -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Godement.LocalSumIdentity

noncomputable section

section

/-! Supported sheaf endomorphisms patch genuine local primitives in the
Godement resolution. The finite sum identity is transported by its additive functor. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.TopCat.Presheaf
open scoped BigOperators

variable {X : TopCat.{0}} {F : TopCat.Sheaf (ModuleCat.{0} ℂ) X}

theorem godementTermMap_apply_zero (f : F ⟶ F) (V : Opens X) (hf : Locality.VanishesOn f V)
    (n : ℕ) (U : Opens X) (a : ((Resolution.godementTerm X n).obj F).obj.obj (op U))
    (x : U) (hx : x.val ∈ V) : (((Resolution.godementTerm X n).map f).hom.app (op U) a) x = 0 := by
  change (stalkFunctor (ModuleCat.{0} ℂ) x.val).map ((Resolution.godementResidual X n).map f).hom (a x) = 0
  rw [Locality.stalkMap_zero_of_vanishesOn _ V (Resolution.godementResidualMap_vanishesOn f V hf n) x.val hx]
  rfl

theorem godement_supported_local_lift (f : F ⟶ F) (U V : Opens X) (hcover : U ⊔ V = ⊤)
    (hf : Locality.VanishesOn f V) (n : ℕ)
    (z : ((Resolution.godementComplex X F).X (n + 1)).obj.obj (op ⊤))
    (a : ((Resolution.godementComplex X F).X n).obj.obj (op U))
    (ha : ((Resolution.godementComplex X F).d n (n + 1)).hom.app (op U) a =
      ((Resolution.godementComplex X F).X (n + 1)).obj.map (homOfLE (show U ≤ ⊤ from le_top)).op z) :
    ∃ t : ((Resolution.godementComplex X F).X n).obj.obj (op ⊤),
      ((Resolution.godementComplex X F).d n (n + 1)).hom.app (op ⊤) t =
        ((Resolution.godementTerm X (n + 1)).map f).hom.app (op ⊤) z := by
  let b := ((Resolution.godementTerm X n).map f).hom.app (op U) a
  refine ⟨SupportedExtension.extendFamily U b, SupportedExtension.map_extendFamily_eq _ U V hcover b _ ?_ ?_ ?_⟩
  · exact fun x hx => godementTermMap_apply_zero f V hf n U a x hx
  · funext x
    exact godementTermMap_apply_zero f V hf (n + 1) ⊤ z ⟨x.val, trivial⟩ x.property
  · have hcomm := ConcreteCategory.congr_hom
      (congrArg (fun g => g.hom.app (op U))
        ((FunctorialResolution.resolutionMap (Godement.Functor.stalkFamilyFunctor X) (Godement.Functor.stalkFamilyUnit X) f).comm n (n + 1))) a
    change ((Resolution.godementComplex X F).d n (n + 1)).hom.app (op U) b =
      ((Resolution.godementTerm X (n + 1)).map f).hom.app (op U)
        (((Resolution.godementComplex X F).d n (n + 1)).hom.app (op U) a) at hcomm
    rw [ha] at hcomm
    exact hcomm.trans (ConcreteCategory.congr_hom
      (((Resolution.godementTerm X (n + 1)).map f).hom.naturality
        (homOfLE (show U ≤ ⊤ from le_top)).op) z)

theorem godement_finite_partition_lift {ι : Type*} [Fintype ι]
    (U V : ι → Opens X) (hcover : ∀ i, U i ⊔ V i = ⊤)
    (f : ι → (F ⟶ F)) (hf : ∀ i, Locality.VanishesOn (f i) (V i)) (hsum : ∑ i, f i = 𝟙 F)
    (n : ℕ) (z : ((Resolution.godementComplex X F).X (n + 1)).obj.obj (op ⊤))
    (a : ∀ i, ((Resolution.godementComplex X F).X n).obj.obj (op (U i)))
    (ha : ∀ i, ((Resolution.godementComplex X F).d n (n + 1)).hom.app (op (U i)) (a i) =
      ((Resolution.godementComplex X F).X (n + 1)).obj.map (homOfLE (show U i ≤ ⊤ from le_top)).op z) :
    ∃ t : ((Resolution.godementComplex X F).X n).obj.obj (op ⊤),
      ((Resolution.godementComplex X F).d n (n + 1)).hom.app (op ⊤) t = z := by
  classical
  choose t ht using fun i => godement_supported_local_lift (f i) (U i) (V i)
    (hcover i) (hf i) n z (a i) (ha i)
  refine ⟨∑ i, t i, ?_⟩
  rw [map_sum]
  simp_rw [ht]
  have hT : (Godement.Functor.stalkFamilyFunctor X).Additive := Godement.Functor.stalkFamilyFunctor_additive
  have hA : (Resolution.godementTerm X (n + 1)).Additive :=
    @FunctorialResolution.resolutionTerm_additive (TopCat.Sheaf (ModuleCat.{0} ℂ) X) _ _
      (Godement.Functor.stalkFamilyFunctor X) (Godement.Functor.stalkFamilyUnit X) hT (n + 1)
  have hmap : ∑ i, (Resolution.godementTerm X (n + 1)).map (f i) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_sum, hsum, CategoryTheory.Functor.map_id]
  let ev : (((Resolution.godementTerm X (n + 1)).obj F) ⟶ ((Resolution.godementTerm X (n + 1)).obj F)) →+
      ((Resolution.godementTerm X (n + 1)).obj F).obj.obj (op ⊤) :=
    { toFun := fun g => g.hom.app (op ⊤) z
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have he := congrArg ev hmap
  rw [map_sum] at he
  exact he

end

/-! A local finite sum identity of sheaf endomorphisms is preserved by
every term of the actual Godement resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open scoped BigOperators

variable {X : TopCat.{0}} {F : TopCat.Sheaf (ModuleCat.{0} ℂ) X} {ι : Type*}

theorem godementTerm_local_sum (f : ι → (F ⟶ F)) (s : Finset ι) (W : Opens X)
    (h : Locality.VanishesOn ((∑ i ∈ s, f i) - 𝟙 _) W) (n : ℕ)
    (a : ((Resolution.godementTerm X n).obj F).obj.obj (op W)) :
    (∑ i ∈ s, ((Resolution.godementTerm X n).map (f i)).hom.app (op W) a) = a := by
  have hT : (Godement.Functor.stalkFamilyFunctor X).Additive := Godement.Functor.stalkFamilyFunctor_additive
  have hA : (Resolution.godementTerm X n).Additive :=
    @FunctorialResolution.resolutionTerm_additive (TopCat.Sheaf (ModuleCat.{0} ℂ) X) _ _
      (Godement.Functor.stalkFamilyFunctor X) (Godement.Functor.stalkFamilyUnit X) hT n
  have hmap : (Resolution.godementTerm X n).map ((∑ i ∈ s, f i) - 𝟙 _) =
      (∑ i ∈ s, (Resolution.godementTerm X n).map (f i)) - 𝟙 _ := by
    rw [CategoryTheory.Functor.map_sub, CategoryTheory.Functor.map_sum, CategoryTheory.Functor.map_id]
  let ev : (((Resolution.godementTerm X n).obj F) ⟶ ((Resolution.godementTerm X n).obj F)) →+
      ((Resolution.godementTerm X n).obj F).obj.obj (op W) :=
    { toFun := fun g => g.hom.app (op W) a
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have he : ev ((Resolution.godementTerm X n).map ((∑ i ∈ s, f i) - 𝟙 _)) = 0 :=
    ConcreteCategory.congr_hom (Resolution.godementTermMap_vanishesOn _ W h n W le_rfl) a
  rw [hmap, map_sub, map_sum] at he
  exact sub_eq_zero.mp he

end

end OAI.AlgebraicGeometry.Comparison.Betti.Godement.LocalSumIdentity
