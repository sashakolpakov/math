import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange

/-! # Open Base Change Naturality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.OpenBaseChangeNaturality.CechOpenBaseChangeNaturality

noncomputable section

/-! The actual Čech comparison for a map of lattices of opens is natural in its coefficients. -/

open _root_.CategoryTheory Limits Opposite Simplicial _root_.AlgebraicTopology

universe w v vD vA u uD uA

variable {A : Type uA} [Category.{vA} A] [Preadditive A] [HasProducts.{w} A]
  {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {D : Type uD} [Category.{vD} D] [Quiver.IsThin D] [HasFiniteProducts D]
  (F : C ⥤ D) [PreservesFiniteLimits F] {ι : Type w} (U : ι → C)

theorem naturality {P Q : Dᵒᵖ ⥤ A} (α : P ⟶ Q) :
    (cechComplexFunctor U).map (Functor.whiskerLeft F.op α) ≫
      (BaseChange.CechBaseChange.complexIso F U Q).hom =
    (BaseChange.CechBaseChange.complexIso F U P).hom ≫
      (cechComplexFunctor (F.obj ∘ U)).map α := by
  ext n : 1
  simp only [HomologicalComplex.comp_f]
  change Limits.Pi.map (fun t : Fin (n + 1) → ι => α.app (op (F.obj (∏ᶜ (U ∘ t))))) ≫
      (Pi.mapIso (fun t : Fin (n + 1) → ι => Q.mapIso (PreservesProduct.iso F (U ∘ t)).symm.op)).hom =
    (Pi.mapIso (fun t : Fin (n + 1) → ι => P.mapIso (PreservesProduct.iso F (U ∘ t)).symm.op)).hom ≫
      Limits.Pi.map (fun t : Fin (n + 1) → ι => α.app (op (∏ᶜ (fun i => F.obj (U (t i))))))
  exact BaseChange.CechBaseChange.productIso_natural
    (fun t : Fin (n + 1) → ι => P.mapIso (PreservesProduct.iso F (U ∘ t)).symm.op)
    (fun t : Fin (n + 1) → ι => Q.mapIso (PreservesProduct.iso F (U ∘ t)).symm.op)
    id (fun t => α.app (op (F.obj (∏ᶜ (U ∘ t)))))
    (fun t => α.app (op (∏ᶜ (fun i => F.obj (U (t i))))))
    (fun t => (α.naturality (PreservesProduct.iso F (U ∘ t)).symm.op.hom).symm)

def iso : (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op ⋙ cechComplexFunctor U ≅
    cechComplexFunctor (F.obj ∘ U) :=
  NatIso.ofComponents (fun P => BaseChange.CechBaseChange.complexIso F U P) (fun {_ _} α => CechOpenBaseChangeNaturality.naturality F U α)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.OpenBaseChangeNaturality.CechOpenBaseChangeNaturality
