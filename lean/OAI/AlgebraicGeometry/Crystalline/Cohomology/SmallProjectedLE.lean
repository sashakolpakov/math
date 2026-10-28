import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.Refinement
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBaseChangeNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.RefinedGeometricCechPullback

/-! # Small Projected LE -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.SmallProjectedLE.SmallProjectedCechPullback

noncomputable section

/-! A cover indexed through compatible source and target opens
gives exactly the original geometric Cech pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial

universe u c v
variable (R : Type u) [CommRing R] {X Y : Scheme.{u}} (f : X ⟶ Y)
  {C : Type c} [Category.{v} C] [HasBinaryProducts C]
  (F : C ⥤ Y.Opens) (G : C ⥤ X.Opens) (tau : G ⟶ F ⋙ RefinedGeometricCechPullback.SmallRefinedGeometricCechPullback.preimage f)
  {ι κ : Type} (U : ι → C) (V : κ → Y.Opens)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) G]
  (r : FormalCoproduct.mk ι (F.obj ∘ U) ⟶ FormalCoproduct.mk κ V)
  {P : RefinedGeometricCechPullback.SmallRefinedGeometricCechPullback.Presheaves R Y} {Q : RefinedGeometricCechPullback.SmallRefinedGeometricCechPullback.Presheaves R X}
  (b : P ⟶ (RefinedGeometricCechPullback.SmallRefinedGeometricCechPullback.functor R f).obj Q)

def transformation : F.op ⋙ P ⟶ G.op ⋙ Q := by
  let bF : F.op ⋙ P ⟶ (F ⋙ RefinedGeometricCechPullback.SmallRefinedGeometricCechPullback.preimage f).op ⋙ Q := Functor.whiskerLeft F.op b
  exact bF ≫ Functor.whiskerRight (NatTrans.op tau) Q

include tau in
omit [HasBinaryProducts C]
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) G] in
theorem coverLE (j : ι) : G.obj (U j) ≤ f ⁻¹ᵁ V (r.f j) :=
  leOfHom (tau.app (U j) ≫ (RefinedGeometricCechPullback.SmallRefinedGeometricCechPullback.preimage f).map (r.φ j))

def map : (NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.complexFunctor V).obj P ⟶
    (NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.complexFunctor (G.obj ∘ U)).obj Q :=
  NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map V (F.obj ∘ U) r P ≫
    (NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBaseChange.NonemptyCechProductBaseChange.complexIso F U P).inv ≫
    (NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.complexFunctor U).map (transformation R f F G tau b) ≫
    (NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBaseChange.NonemptyCechProductBaseChange.complexIso G U Q).hom

theorem projection (n : ℕ) (t : Fin (n + 1) → ι) :
    (SmallProjectedCechPullback.map R f F G tau U V r b).f n ≫
      Pi.π (fun t : Fin (n + 1) → ι => Q.obj (op (∏ᶜ ((G.obj ∘ U) ∘ t)))) t =
    Pi.π (fun s : Fin (n + 1) → κ => P.obj (op (∏ᶜ (V ∘ s)))) (r.f ∘ t) ≫
      P.map ((FormalCoproduct.powerMap r (Fin (n + 1))).φ t).op ≫
      P.map (PreservesProduct.iso F (U ∘ t)).op.hom ≫
      b.app (op (F.obj (∏ᶜ (U ∘ t)))) ≫
      Q.map (tau.app (∏ᶜ (U ∘ t))).op ≫
      Q.map (PreservesProduct.iso G (U ∘ t)).symm.op.hom := by
  change (Pi.lift (fun s : Fin (n + 1) → ι =>
      Pi.π (fun a : Fin (n + 1) → κ => P.obj (op (∏ᶜ (V ∘ a)))) (r.f ∘ s) ≫
        P.map ((FormalCoproduct.powerMap r (Fin (n + 1))).φ s).op) ≫
      Limits.Pi.map (fun s : Fin (n + 1) → ι => P.map (PreservesProduct.iso F (U ∘ s)).op.hom) ≫
      Limits.Pi.map (fun s : Fin (n + 1) → ι =>
        b.app (op (F.obj (∏ᶜ (U ∘ s)))) ≫ Q.map (tau.app (∏ᶜ (U ∘ s))).op) ≫
      Limits.Pi.map (fun s : Fin (n + 1) → ι => Q.map (PreservesProduct.iso G (U ∘ s)).symm.op.hom)) ≫ _ = _
  simp only [Category.assoc]
  erw [Pi.map_π, Pi.map_π_assoc, Pi.map_π_assoc, Pi.lift_comp_π_assoc]
  exact congrArg (fun x => Pi.π (fun s : Fin (n + 1) → κ => P.obj (op (∏ᶜ (V ∘ s)))) (r.f ∘ t) ≫
    P.map ((FormalCoproduct.powerMap r (Fin (n + 1))).φ t).op ≫
    P.map (PreservesProduct.iso F (U ∘ t)).op.hom ≫ x)
    (Category.assoc (b.app (op (F.obj (∏ᶜ (U ∘ t))))) (Q.map (tau.app (∏ᶜ (U ∘ t))).op)
      (Q.map (PreservesProduct.iso G (U ∘ t)).symm.op.hom))

theorem compatibility : SmallProjectedCechPullback.map R f F G tau U V r b =
    RefinedGeometricCechPullback.SmallRefinedGeometricCechPullback.map R f V (G.obj ∘ U) r.f (coverLE f F G tau U V r) b := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply Pi.hom_ext
  intro t
  change Fin (n + 1) → ι at t
  let a := ((FormalCoproduct.powerMap r (Fin (n + 1))).φ t)
  let e := (PreservesProduct.iso F (U ∘ t)).hom
  let c := (PreservesProduct.iso G (U ∘ t)).inv
  let d := RefinedGeometricCechPullback.SmallRefinedGeometricCechPullback.intersectionHom f V (G.obj ∘ U) r.f (coverLE f F G tau U V r) n t
  let v := op (∏ᶜ (V ∘ (r.f ∘ t)))
  let w := op (F.obj (∏ᶜ (U ∘ t)))
  let z := tau.app (∏ᶜ (U ∘ t))
  have hp : P.map a.op ≫ P.map e.op = P.map (e ≫ a).op := (P.map_comp _ _).symm
  have hb : P.map (e ≫ a).op ≫ b.app w = b.app v ≫ Q.map ((RefinedGeometricCechPullback.SmallRefinedGeometricCechPullback.preimage f).map (e ≫ a)).op :=
    b.naturality (e ≫ a).op
  have hq : Q.map ((RefinedGeometricCechPullback.SmallRefinedGeometricCechPullback.preimage f).map (e ≫ a)).op ≫ Q.map z.op ≫ Q.map c.op = Q.map d.op :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun x => x ≫ Q.map c.op) (Q.map_comp _ _).symm).trans
        ((Q.map_comp _ _).symm.trans (congrArg Q.map (Subsingleton.elim _ _))))
  have hc : P.map a.op ≫ P.map e.op ≫ b.app w ≫ Q.map z.op ≫ Q.map c.op = b.app v ≫ Q.map d.op :=
    (Category.assoc (P.map a.op) (P.map e.op) (b.app w ≫ Q.map z.op ≫ Q.map c.op)).symm.trans
      ((congrArg (fun x => x ≫ b.app w ≫ Q.map z.op ≫ Q.map c.op) hp).trans
        ((Category.assoc (P.map (e ≫ a).op) (b.app w) (Q.map z.op ≫ Q.map c.op)).symm.trans
          ((congrArg (fun x => x ≫ Q.map z.op ≫ Q.map c.op) hb).trans
            ((Category.assoc (b.app v) (Q.map ((RefinedGeometricCechPullback.SmallRefinedGeometricCechPullback.preimage f).map (e ≫ a)).op)
              (Q.map z.op ≫ Q.map c.op)).trans (congrArg (fun x => b.app v ≫ x) hq)))))
  exact (projection R f F G tau U V r b n t).trans
    ((congrArg (fun x => Pi.π (fun s : Fin (n + 1) → κ => P.obj (op (∏ᶜ (V ∘ s)))) (r.f ∘ t) ≫ x) hc).trans
      (RefinedGeometricCechPullback.SmallRefinedGeometricCechPullback.map_f_π R f V (G.obj ∘ U) r.f (coverLE f F G tau U V r) b n t).symm)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.SmallProjectedLE.SmallProjectedCechPullback
