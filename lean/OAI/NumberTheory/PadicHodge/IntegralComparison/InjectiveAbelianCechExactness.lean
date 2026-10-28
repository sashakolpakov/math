import OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveFrameCechExactness
import OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.IntegerSheafEquivalence

/-! # Injective Abelian Cech Exactness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveAbelianCechExactness

noncomputable section

/-! Positive Čech cocycles with injective additive-sheaf coefficients
have primitives, in the coefficient universes of native sheaf cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v
variable {C : Type (max u v)} [Category.{v} C] [HasBinaryProducts C]
  {ι : Type v} (F : ι → C) (J : GrothendieckTopology C)
  (H : Sheaf J AddCommGrpCat.{max u v})

open OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.IntegerSheafEquivalence

def sectionEquiv (V : C) :
    (Lifted.IntegerSheafEquivalence.moduleSheaf J H).obj.obj (op V) ≃+ H.obj.obj (op V) :=
  CategoryTheory.Iso.addCommGroupIsoToAddEquiv
    (((sheafToPresheaf J AddCommGrpCat.{max u v}) ⋙ (evaluation _ _).obj (op V)).mapIso
      (Lifted.IntegerSheafEquivalence.moduleSheafIso J H))

omit [HasBinaryProducts C] in
theorem sectionEquiv_naturality {V W : C} (f : V ⟶ W)
    (x : (Lifted.IntegerSheafEquivalence.moduleSheaf J H).obj.obj (op W)) :
    sectionEquiv J H V ((Lifted.IntegerSheafEquivalence.moduleSheaf J H).obj.map f.op x) =
      H.obj.map f.op (sectionEquiv J H W x) :=
  NatTrans.naturality_apply (Lifted.IntegerSheafEquivalence.moduleSheafIso J H).hom.hom f.op x

variable [Injective H]

theorem boundary (hcover : ∀ U, CoveringObjectsSheafDetection.sieve F U ∈ J U) (n : ℕ)
    (x : ∀ t : Fin (n + 2) → ι,
      H.obj.obj (op (Presentation.TupleProducts.family F (n + 1) t)))
    (hx : ∀ t : Fin (n + 3) → ι,
      (∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) •
        H.obj.map (Presentation.ResolutionFaceMaps.productMap F i.succAbove t).op
          (x (t ∘ i.succAbove))) = 0) :
    ∃ y : ∀ t : Fin (n + 1) → ι,
      H.obj.obj (op (Presentation.TupleProducts.family F n t)),
      ∀ t : Fin (n + 2) → ι,
        (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          H.obj.map (Presentation.ResolutionFaceMaps.productMap F i.succAbove t).op
            (y (t ∘ i.succAbove))) = x t := by
  let M := Lifted.IntegerSheafEquivalence.moduleSheaf J H
  let e := sectionEquiv J H
  let c := fun t : Fin (n + 2) → ι =>
    (e (Presentation.TupleProducts.family F (n + 1) t)).symm (x t)
  have hc : ∀ t : Fin (n + 3) → ι,
      (∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) •
        M.obj.map (Presentation.ResolutionFaceMaps.productMap F i.succAbove t).op
          (c (t ∘ i.succAbove))) = 0 := by
    intro t
    apply (e (Presentation.TupleProducts.family F (n + 2) t)).injective
    rw [map_sum, map_zero]
    simp only [map_zsmul, e, M, sectionEquiv_naturality, c, AddEquiv.apply_symm_apply]
    exact hx t
  obtain ⟨b, hb⟩ := InjectiveFrameCechExactness.boundary_coordinates F
    (ULift.{max u v} ℤ) J hcover M n c hc
  refine ⟨fun t => e _ (b t), fun t => ?_⟩
  have he := congrArg (e (Presentation.TupleProducts.family F (n + 1) t)) (hb t)
  rw [map_sum] at he
  simpa only [map_zsmul, e, M, sectionEquiv_naturality, c, AddEquiv.apply_symm_apply] using he

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveAbelianCechExactness
