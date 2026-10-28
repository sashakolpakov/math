import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.ConeCechMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CohomologyProduct

/-! # Cone Cech Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.ConeCechCohomology

noncomputable section

/-! Actual constant-cochain Čech augmentation preserves the induced
categorical cohomology product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  (R : Type u) [CommRing R] {ι : Type} [Finite ι] (F : ι → C)
  (M : CochainComplex (ModuleCat.{u} R) ℕ)
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ)
  (a : ((Functor.const Cᵒᵖ).mapHomologicalComplex (.up ℕ)).obj M ⟶ P)
  (μ : ∀ i j V, (P.X i).obj V →ₗ[R] (P.X j).obj V →ₗ[R] (P.X (i+j)).obj V)
  (hμ : ∀ i j {V W : Cᵒᵖ} (f : V ⟶ W) x y,
    (P.X (i+j)).map f (μ i j V x y) = μ i j W ((P.X i).map f x) ((P.X j).map f y))
  (dμ : ∀ i j V x y,
    (P.d (i+j) (i+j+1)).app V (μ i j V x y) =
      CechProduct.sectionDegreeCast P (by omega : (i+1)+j=i+j+1) V
        (μ (i+1) j V ((P.d i (i+1)).app V x) y) +
      (-1 : ℤ)^i • CechProduct.sectionDegreeCast P (by omega : i+(j+1)=i+j+1) V
        (μ i (j+1) V x ((P.d j (j+1)).app V y)))
  (σ : ∀ i j, M.X i →ₗ[R] M.X j →ₗ[R] M.X (i+j))
  (dσ : ∀ i j x y, M.d (i+j) (i+j+1) (σ i j x y) =
    Cochain.CohomologyCup.cupInto M σ (i+1) j (i+j+1) (by omega)
      (M.d i (i+1) x) y +
    (-1 : ℤ)^i • Cochain.CohomologyCup.cupInto M σ i (j+1) (i+j+1) (by omega)
      x (M.d j (j+1) y))
  (ha : ∀ i j V x y, (a.f (i+j)).app V (σ i j x y) =
    μ i j V ((a.f i).app V x) ((a.f j).app V y))

abbrev map_cup := Cochain.CupNaturality.Cohomology.cohomologyMap_cup σ
  (TotalCup.CechProduct.totalCup (NonemptyCechNerve.nerve F) P μ) dσ
  (TotalLeibniz.CechProduct.differential_totalCup (NonemptyCechNerve.nerve F) P μ hμ dμ)
  (ConeCechMap.map R F M P a)
  (ConeCechMap.map_cup R F M P a μ σ ha)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.ConeCechCohomology
