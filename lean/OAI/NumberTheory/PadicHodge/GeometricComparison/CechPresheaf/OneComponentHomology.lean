import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedHomotopy
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ComponentHomology

/-! # One Component Homology -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.OneComponentHomology.CechPresheafHOneComponentHomology

noncomputable section

/-! Component equality gives equality and refinement naturality
in the original typed presheaf Cech H-one coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v s t a b
variable (R : Type u) [CommRing R]
  {C : Type s} [Category.{t} C] [HasBinaryProducts C]
  {ι : Type} (U : ι → C)
  {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ}
  (f g : K ⟶ L) (h : ∀ q, q ≤ 1 → ∀ W, (f.f q).app W = (g.f q).app W)

include h in
theorem homology : RefinedHomotopy.CechPresheafRefinedHomotopy.mapHOne R U f =
    RefinedHomotopy.CechPresheafRefinedHomotopy.mapHOne R U g :=
  ComponentHomology.CechPresheafComponentHomology.homology R (IntegralComparison.NonemptyCechNerve.nerve U) f g 1 h

variable {D : Type a} [Category.{b} D] [Quiver.IsThin D] [HasBinaryProducts D]
  (F : C ⥤ D) {κ : Type} (V : κ → D)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  (r : FormalCoproduct.mk ι (F.obj ∘ U) ⟶ FormalCoproduct.mk κ V)

variable {M N : CochainComplex (Dᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ}
  (a : M ⟶ N)
  (b : ((RefinedHomotopy.CechPresheafRefinedHomotopy.pullback R F).mapHomologicalComplex (.up ℕ)).obj M ⟶
    ((RefinedHomotopy.CechPresheafRefinedHomotopy.pullback R F).mapHomologicalComplex (.up ℕ)).obj N)
  (hb : ∀ q, q ≤ 1 → ∀ W,
    ((((RefinedHomotopy.CechPresheafRefinedHomotopy.pullback R F).mapHomologicalComplex (.up ℕ)).map a).f q).app W =
      (b.f q).app W)

include hb in
theorem refinement_homology : RefinedHomotopy.CechPresheafRefinedHomotopy.mapHOne R V a ≫
    RefinedHomotopy.CechPresheafRefinedHomotopy.refinementHOne R F U V r N =
      RefinedHomotopy.CechPresheafRefinedHomotopy.refinementHOne R F U V r M ≫
        RefinedHomotopy.CechPresheafRefinedHomotopy.mapHOne R U b :=
  (RefinedHomotopy.CechPresheafRefinedHomotopy.refinement_homology R F U V r a).trans
    (congrArg (fun c => RefinedHomotopy.CechPresheafRefinedHomotopy.refinementHOne R F U V r M ≫ c)
      (homology R U (((RefinedHomotopy.CechPresheafRefinedHomotopy.pullback R F).mapHomologicalComplex (.up ℕ)).map a) b hb))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.OneComponentHomology.CechPresheafHOneComponentHomology
