import OAI.AlgebraicGeometry.Comparison.Betti.Godement.Functor

/-! # Supported Extension -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Godement.SupportedExtension

noncomputable section

/-! Actual extension by zero of stalk families, and compatibility with a
sheaf differential when the section vanishes on the complementary open set. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable {X : TopCat.{0}} {F G : TopCat.Sheaf (ModuleCat.{0} ℂ) X}

def extendFamily (U : Opens X) (s : (HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions.stalkFamilySheaf F).obj.obj (op U)) :
    (HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions.stalkFamilySheaf F).obj.obj (op ⊤) := by
  classical
  exact fun x => if hx : x.val ∈ U then s ⟨x.val, hx⟩ else 0

theorem extendFamily_restrict (U : Opens X) (s : (HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions.stalkFamilySheaf F).obj.obj (op U)) :
    (HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions.stalkFamilySheaf F).obj.map (homOfLE (show U ≤ ⊤ from le_top)).op (extendFamily U s) = s := by
  classical
  funext x
  exact dite_eq_left x.property

theorem extendFamily_zero (U V : Opens X) (s : (HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions.stalkFamilySheaf F).obj.obj (op U))
    (hs : ∀ x : U, x.val ∈ V → s x = 0) :
    (HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions.stalkFamilySheaf F).obj.map (homOfLE (show V ≤ ⊤ from le_top)).op (extendFamily U s) = 0 := by
  classical
  funext x
  change (if hx : x.val ∈ U then s ⟨x.val, hx⟩ else (0 : F.presheaf.stalk x.val)) = 0
  split_ifs with hx
  · exact hs ⟨x.val, hx⟩ x.property
  · rfl

theorem map_extendFamily_eq (d : HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions.stalkFamilySheaf F ⟶ HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions.stalkFamilySheaf G)
    (U V : Opens X) (hcover : U ⊔ V = ⊤)
    (s : (HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions.stalkFamilySheaf F).obj.obj (op U))
    (b : (HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions.stalkFamilySheaf G).obj.obj (op ⊤))
    (hs : ∀ x : U, x.val ∈ V → s x = 0)
    (hb : (HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions.stalkFamilySheaf G).obj.map (homOfLE (show V ≤ ⊤ from le_top)).op b = 0)
    (hd : d.hom.app (op U) s =
      (HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions.stalkFamilySheaf G).obj.map (homOfLE (show U ≤ ⊤ from le_top)).op b) :
    d.hom.app (op ⊤) (extendFamily U s) = b := by
  funext x
  have hx : x.val ∈ U ⊔ V := by rw [hcover]; trivial
  rcases hx with hx | hx
  · have hnat := ConcreteCategory.congr_hom
      (d.hom.naturality (homOfLE (show U ≤ ⊤ from le_top)).op) (extendFamily U s)
    change d.hom.app (op U)
      ((HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions.stalkFamilySheaf F).obj.map (homOfLE (show U ≤ ⊤ from le_top)).op (extendFamily U s)) =
      (HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions.stalkFamilySheaf G).obj.map (homOfLE (show U ≤ ⊤ from le_top)).op
        (d.hom.app (op ⊤) (extendFamily U s)) at hnat
    rw [extendFamily_restrict, hd] at hnat
    exact (congrFun hnat ⟨x.val, hx⟩).symm
  · have hnat := ConcreteCategory.congr_hom
      (d.hom.naturality (homOfLE (show V ≤ ⊤ from le_top)).op) (extendFamily U s)
    change d.hom.app (op V)
      ((HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions.stalkFamilySheaf F).obj.map (homOfLE (show V ≤ ⊤ from le_top)).op (extendFamily U s)) =
      (HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions.stalkFamilySheaf G).obj.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (d.hom.app (op ⊤) (extendFamily U s)) at hnat
    rw [extendFamily_zero U V s hs, map_zero] at hnat
    exact (congrFun hnat ⟨x.val, hx⟩).symm.trans (congrFun hb ⟨x.val, hx⟩).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.Godement.SupportedExtension
