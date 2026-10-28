import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Edges
import OAI.NumberTheory.PadicHodge.IntegralComparison.TotalComponentMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.DualComplexHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KoszulHomotopy

/-! # Components -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components

noncomputable section

/-! Literal components of the mixed Koszul-to-supported-Čech total map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Differential
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.CechDifferential OAI.AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c m : ℕ} (U : ULift.{u} (Fin m) → C)
  (s : Fin c → R) (t : Fin m → R)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))

abbrev source := DualComplexHomology.complex R
  (Exterior.KoszulComplex.complex R (Fractions.ambient R (c := c) (m := m)) (Differential.equation R s t))
abbrev coefficient := Koszul.HomPresheaf.complex R (Fractions.normal R (c := c))
  (Fractions.modules R P) (Koszul.GeneratorMatrix.equation R s)
abbrev target := AugmentedOrdered.CechFunctor.bicomplex U (coefficient R P s)

def coordinateAt (n p q : ℕ) (h : p + q = n) (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q) :
    Module.Dual R (⋀[R]^n (Fractions.ambient R (c := c) (m := m))) →ₗ[R]
      ((⋀[R]^p (Fractions.normal R (c := c))) →ₗ[R] P.obj (op ((AugmentedOrdered.Cech.formal U q).obj a))) where
  toFun φ := Fractions.reciprocal R P U t ht a •
    (Algebra.linearMap R _).comp (φ.comp (Differential.insertionAt R p q n h a))
  map_add' φ ψ := by
    apply LinearMap.ext
    intro x
    change Fractions.reciprocal R P U t ht a * algebraMap R _ ((φ + ψ) (Differential.insertionAt R p q n h a x)) = _
    simp only [LinearMap.add_apply, map_add, mul_add, LinearMap.comp_apply,
      LinearMap.smul_apply, smul_eq_mul]
    rfl
  map_smul' r φ := by
    apply LinearMap.ext
    intro x
    change Fractions.reciprocal R P U t ht a * algebraMap R _ ((r • φ) (Differential.insertionAt R p q n h a x)) = _
    simp only [LinearMap.smul_apply, RingHom.id_apply, Algebra.smul_def,
      map_mul, LinearMap.comp_apply, Algebra.algebraMap_self, Algebra.linearMap_apply]
    ring

theorem coordinateAt_apply (n p q : ℕ) (h : p + q = n) (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q)
    (φ : (source R s t).X n) (x : ⋀[R]^p (Fractions.normal R (c := c))) :
    coordinateAt R P U t ht n p q h a φ x = CechDifferential.value R P U t ht p q n h a φ x := rfl

def component (n p q : ℕ) (h : p + q = n) :
    ModuleCat.of R (Module.Dual R (⋀[R]^n (Fractions.ambient R (c := c) (m := m)))) ⟶
      AugmentedOrdered.Cech.object U (Koszul.HomPresheaf.homPresheaf R (Fractions.normal R (c := c)) (Fractions.modules R P) p) q :=
  Pi.lift (fun a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q => ModuleCat.ofHom (coordinateAt R P U t ht n p q h a))

@[reassoc]
theorem component_projection (n p q : ℕ) (h : p + q = n) (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q) :
    component R P U t ht n p q h ≫
      Pi.π (fun b : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q =>
        ((coefficient R P s).X p).obj (op ((AugmentedOrdered.Cech.formal U q).obj b))) a =
    ModuleCat.ofHom (coordinateAt R P U t ht n p q h a) := Pi.lift_comp_π _ a

theorem source_d (n : ℕ) : ((source R s t).d n (n + 1)).hom =
    (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R _ (Differential.equation R s t) n).dualMap := by
  dsimp only [source, DualComplexHomology.complex, Functor.mapHomologicalComplex_obj_d,
    HomologicalComplex.op_d, ExactModuleDualFunctor.functor]
  rw [Exterior.KoszulHomotopy.complex_d]
  rfl

theorem vertical_d (p q : ℕ) : ((target R P U s).X p).d q (q + 1) =
    AugmentedOrdered.Cech.differential U ((coefficient R P s).X p) q := by
  change (AugmentedOrdered.Cech.complex U ((coefficient R P s).X p)).d q (q + 1) = _
  dsimp only [AugmentedOrdered.Cech.complex]
  rw [CochainComplex.of_d]

theorem horizontal_d (p q : ℕ) : ((target R P U s).d p (p + 1)).f q =
    AugmentedOrdered.CechFunctor.objectMap U (Koszul.HomPresheaf.differential R (Fractions.normal R (c := c)) (Fractions.modules R P)
      (Koszul.GeneratorMatrix.equation R s) p) q := by
  change AugmentedOrdered.CechFunctor.objectMap U ((coefficient R P s).d p (p + 1)) q = _
  dsimp only [coefficient, Koszul.HomPresheaf.complex]
  rw [CochainComplex.of_d]

theorem horizontal_projection (p q : ℕ) (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q) :
    ((target R P U s).d p (p + 1)).f q ≫
      Pi.π (fun b : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q =>
        ((coefficient R P s).X (p + 1)).obj (op ((AugmentedOrdered.Cech.formal U q).obj b))) a =
    Pi.π (fun b : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q =>
        ((coefficient R P s).X p).obj (op ((AugmentedOrdered.Cech.formal U q).obj b))) a ≫
      (Koszul.HomPresheaf.differential R (Fractions.normal R (c := c)) (Fractions.modules R P)
        (Koszul.GeneratorMatrix.equation R s) p).app (op ((AugmentedOrdered.Cech.formal U q).obj a)) := by
  change AugmentedOrdered.CechFunctor.objectMap U ((coefficient R P s).d p (p + 1)) q ≫ _ = _
  rw [AugmentedOrdered.CechCoordinates.objectMap_comp_pi]
  dsimp only [coefficient, Koszul.HomPresheaf.complex]
  rw [CochainComplex.of_d]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
