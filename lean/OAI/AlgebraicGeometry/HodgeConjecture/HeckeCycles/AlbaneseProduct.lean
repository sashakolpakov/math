import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Products
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-! # Albanese Product -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseProduct.CM

noncomputable section

/-! Smoothness, properness, and geometric connectedness of TateComparison's actual
total Albanese product follow from IntegralModel's component geometry. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

def GoodGroupGeometry {S : Scheme} (A : Over S) : Prop :=
  Smooth A.hom ∧ IsProper A.hom ∧ GeometricallyConnected A.hom

theorem geometry_of_iso {S : Scheme} {A B : Over S} (e : A ≅ B)
    (hB : GoodGroupGeometry B) : GoodGroupGeometry A := by
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  let : Smooth B.hom := hB.1
  let : IsProper B.hom := hB.2.1
  let : MorphismProperty.RespectsIso (@GeometricallyConnected) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  dsimp only [GoodGroupGeometry]
  rw [← e.hom.w]
  exact ⟨inferInstance, inferInstance,
    (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected _ _).mpr hB.2.2⟩

theorem identity_geometry (S : Scheme) : GoodGroupGeometry (Over.mk (𝟙 S)) := by
  change Smooth (𝟙 S) ∧ IsProper (𝟙 S) ∧ GeometricallyConnected (𝟙 S)
  refine ⟨inferInstance, inferInstance, ?_⟩
  constructor
  intro K _ x Z fst snd hp
  let : IsIso snd := hp.isIso_snd_of_isIso
  exact (asIso snd).hom.homeomorph.connectedSpace_iff.mpr inferInstance

theorem binary_geometry {S : Scheme} (A B : Over S)
    (hA : GoodGroupGeometry A) (hB : GoodGroupGeometry B) :
    GoodGroupGeometry (A ⨯ B) := by
  let : Smooth A.hom := hA.1
  let : Smooth B.hom := hB.1
  let : IsProper B.hom := hB.2.1
  let : GeometricallyConnected B.hom := hB.2.2
  have hp := Over.isPullback_of_binaryFan_isLimit _ (prodIsProd A B)
  let f : A ⨯ B ⟶ B := prod.snd
  let : Smooth f.left := MorphismProperty.of_isPullback hp hA.1
  let : IsProper f.left := MorphismProperty.of_isPullback hp hA.2.1
  let : GeometricallyConnected f.left := MorphismProperty.of_isPullback hp hA.2.2
  change Smooth (A ⨯ B).hom ∧ IsProper (A ⨯ B).hom ∧
    GeometricallyConnected (A ⨯ B).hom
  rw [← f.w]
  exact ⟨inferInstance, inferInstance, GeometricallyConnected.comp f.left B.hom⟩

theorem finite_product_geometry {S : Scheme} (r : ℕ) (A : Fin r → Over S)
    (hA : ∀ i, GoodGroupGeometry (A i)) : GoodGroupGeometry (∏ᶜ A) := by
  induction r with
  | zero =>
    let c : Fan A := Fan.mk (Over.mk (𝟙 S)) (fun i => Fin.elim0 i)
    have hc : IsLimit c := Fan.IsLimit.mk _
      (fun c' => Over.mkIdTerminal.from c'.pt)
      (fun _ i => Fin.elim0 i)
      (fun _ _ _ => Over.mkIdTerminal.hom_ext _ _)
    exact geometry_of_iso ((limit.isLimit _).conePointUniqueUpToIso hc)
      (identity_geometry S)
  | succ r ih =>
    have ht := ih (fun i => A i.succ) (fun i => hA i.succ)
    have hp := binary_geometry (A 0) (∏ᶜ fun i : Fin r => A i.succ) (hA 0) ht
    have hc := extendFanIsLimit A (limit.isLimit (Discrete.functor fun i : Fin r => A i.succ))
      (prodIsProd (A 0) (∏ᶜ fun i : Fin r => A i.succ))
    exact geometry_of_iso ((limit.isLimit _).conePointUniqueUpToIso hc) hp

/-- This is the exact group product used to define TateComparison's endomorphism
algebra, identified with the finite scheme product by its canonical iso. -/
theorem component_product_geometry {S : Scheme} {r : ℕ}
    (A : Fin r → CommGrp (Over S)) (hA : ∀ i, GoodGroupGeometry (A i).X) :
    GoodGroupGeometry (AbelianScheme.TateComparison.Products.componentProduct A).X :=
  geometry_of_iso (AbelianScheme.TateComparison.Products.componentProductComparison A)
    (finite_product_geometry r (fun i => (A i).X) hA)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseProduct.CM
