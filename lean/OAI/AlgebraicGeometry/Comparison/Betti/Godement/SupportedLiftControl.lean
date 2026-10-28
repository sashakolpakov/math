import OAI.AlgebraicGeometry.Comparison.Betti.Godement.LocalSumIdentity

/-! # Supported Lift Control -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Godement.SupportedLiftControl

noncomputable section

/-! Supported local primitives with an explicit vanishing statement for
their actual global stalk families. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable {X : TopCat.{0}} {F : TopCat.Sheaf (ModuleCat.{0} ℂ) X}

theorem godement_supported_local_lift_control (f : F ⟶ F) (U V : Opens X)
    (hcover : U ⊔ V = ⊤) (hf : Locality.VanishesOn f V) (n : ℕ)
    (z : ((Resolution.godementComplex X F).X (n + 1)).obj.obj (op ⊤))
    (a : ((Resolution.godementComplex X F).X n).obj.obj (op U))
    (ha : ((Resolution.godementComplex X F).d n (n + 1)).hom.app (op U) a =
      ((Resolution.godementComplex X F).X (n + 1)).obj.map (homOfLE (show U ≤ ⊤ from le_top)).op z) :
    ∃ t : ((Resolution.godementComplex X F).X n).obj.obj (op ⊤),
      ((Resolution.godementComplex X F).d n (n + 1)).hom.app (op ⊤) t =
        ((Resolution.godementTerm X (n + 1)).map f).hom.app (op ⊤) z ∧
      ∀ x : (⊤ : Opens X), x.val ∈ V → t x = 0 := by
  let b := ((Resolution.godementTerm X n).map f).hom.app (op U) a
  have hb : ∀ x : U, x.val ∈ V → b x = 0 :=
    fun x hx => LocalSumIdentity.godementTermMap_apply_zero f V hf n U a x hx
  refine ⟨SupportedExtension.extendFamily U b, ?_, ?_⟩
  · apply SupportedExtension.map_extendFamily_eq _ U V hcover b _ hb
    · funext x
      exact LocalSumIdentity.godementTermMap_apply_zero f V hf (n + 1) ⊤ z ⟨x.val, trivial⟩ x.property
    · have hcomm := ConcreteCategory.congr_hom
        (congrArg (fun g => g.hom.app (op U))
          ((FunctorialResolution.resolutionMap (Functor.stalkFamilyFunctor X) (Functor.stalkFamilyUnit X) f).comm n (n + 1))) a
      change ((Resolution.godementComplex X F).d n (n + 1)).hom.app (op U) b =
        ((Resolution.godementTerm X (n + 1)).map f).hom.app (op U)
          (((Resolution.godementComplex X F).d n (n + 1)).hom.app (op U) a) at hcomm
      rw [ha] at hcomm
      exact hcomm.trans (ConcreteCategory.congr_hom
        (((Resolution.godementTerm X (n + 1)).map f).hom.naturality
          (homOfLE (show U ≤ ⊤ from le_top)).op) z)
  · intro x hx
    exact congrFun (SupportedExtension.extendFamily_zero U V b hb) ⟨x.val, hx⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.Godement.SupportedLiftControl
