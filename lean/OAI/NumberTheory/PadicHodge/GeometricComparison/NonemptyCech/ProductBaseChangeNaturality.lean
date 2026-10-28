import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBaseChange

/-! # Product Base Change Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBaseChangeNaturality.NonemptyCechProductBaseChangeNaturality

noncomputable section

/-! The original nonempty Cech base-change comparison is natural in its coefficients. -/

open _root_.CategoryTheory Limits Opposite Simplicial _root_.AlgebraicTopology

universe w v vD vA u uD uA

variable {A : Type uA} [Category.{vA} A] [Preadditive A] [HasProducts.{w} A]
  {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type uD} [Category.{vD} D] [Quiver.IsThin D] [HasBinaryProducts D]
  (F : C ⥤ D) {ι : Type w} (U : ι → C)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]

theorem naturality {P Q : Dᵒᵖ ⥤ A} (α : P ⟶ Q) :
    (IntegralComparison.NonemptyCechNerve.complexFunctor U).map (Functor.whiskerLeft F.op α) ≫
      (ProductBaseChange.NonemptyCechProductBaseChange.complexIso F U Q).hom =
    (ProductBaseChange.NonemptyCechProductBaseChange.complexIso F U P).hom ≫
      (IntegralComparison.NonemptyCechNerve.complexFunctor (F.obj ∘ U)).map α := by
  ext n : 1
  simp only [HomologicalComplex.comp_f]
  change Limits.Pi.map (fun t : Fin (n + 1) → ι => α.app (op (F.obj (∏ᶜ (U ∘ t))))) ≫
      (Pi.mapIso (fun t : Fin (n + 1) → ι => Q.mapIso (PreservesProduct.iso F (U ∘ t)).symm.op)).hom =
    (Pi.mapIso (fun t : Fin (n + 1) → ι => P.mapIso (PreservesProduct.iso F (U ∘ t)).symm.op)).hom ≫
      Limits.Pi.map (fun t : Fin (n + 1) → ι => α.app (op (∏ᶜ (fun i => F.obj (U (t i))))))
  change Limits.Pi.map (fun t : Fin (n + 1) → ι => α.app (op (F.obj (∏ᶜ (U ∘ t))))) ≫
      Limits.Pi.map (fun t : Fin (n + 1) → ι => Q.map (PreservesProduct.iso F (U ∘ t)).symm.op.hom) =
    Limits.Pi.map (fun t : Fin (n + 1) → ι => P.map (PreservesProduct.iso F (U ∘ t)).symm.op.hom) ≫
      Limits.Pi.map (fun t : Fin (n + 1) → ι => α.app (op (∏ᶜ (fun i => F.obj (U (t i))))))
  rw [Limits.Pi.map_comp_map, Limits.Pi.map_comp_map]
  congr 1
  funext t
  exact (α.naturality (PreservesProduct.iso F (U ∘ t)).symm.op.hom).symm

def iso : (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op ⋙ IntegralComparison.NonemptyCechNerve.complexFunctor U ≅
    IntegralComparison.NonemptyCechNerve.complexFunctor (F.obj ∘ U) :=
  NatIso.ofComponents (fun P => ProductBaseChange.NonemptyCechProductBaseChange.complexIso F U P) (fun {_ _} α => NonemptyCechProductBaseChangeNaturality.naturality F U α)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBaseChangeNaturality.NonemptyCechProductBaseChangeNaturality
