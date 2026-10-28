import OAI.NumberTheory.PadicHodge.IntegralComparison.CentralNullHomotopy
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components

/-! # Punctured Homotopy -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.PuncturedHomotopy

noncomputable section

/-! On any principal intersection where one point parameter is a unit,
every map from the genuine point dual Koszul complex is nullhomotopic.
The inverse coefficient and wedge homotopy are explicit. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Differential
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c m : ℕ} (s : Fin c → R) (t : Fin m → R)

abbrev coefficientAt (a : Cᵒᵖ) :=
  (((evaluation Cᵒᵖ (ModuleCat R)).obj a).mapHomologicalComplex (.up ℕ)).obj (KoszulPartial.Components.coefficient R P s)

def multiply (a : Cᵒᵖ) (z : P.obj a) : coefficientAt R P s a ⟶ coefficientAt R P s a where
  f n := ModuleCat.ofHom
    { toFun := fun φ => (LinearMap.mulLeft R z).comp
        (show (⋀[R]^n (KoszulPartial.Fractions.normal R (c := c))) →ₗ[R] P.obj a from φ)
      map_add' := by
        intro φ ψ
        change (⋀[R]^n (KoszulPartial.Fractions.normal R (c := c))) →ₗ[R] P.obj a at φ ψ
        apply LinearMap.ext
        intro x
        change z * (φ x + ψ x) = z * φ x + z * ψ x
        exact mul_add _ _ _
      map_smul' := by
        intro r φ
        change (⋀[R]^n (KoszulPartial.Fractions.normal R (c := c))) →ₗ[R] P.obj a at φ
        apply LinearMap.ext
        intro x
        change z * (r • φ x) = r • (z * φ x)
        simp only [Algebra.smul_def]
        ring }
  comm' i j hij := by
    have hj : i + 1 = j := hij
    subst j
    change _ ≫ ((KoszulPartial.Components.coefficient R P s).d i (i + 1)).app a =
      ((KoszulPartial.Components.coefficient R P s).d i (i + 1)).app a ≫ _
    dsimp only [KoszulPartial.Components.coefficient, HomPresheaf.complex]
    rw [CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro x
    rfl

omit [HasFiniteProducts C] in
theorem multiply_inverse (a : Cᵒᵖ) (r : R) (z : P.obj a)
    (hz : algebraMap R (P.obj a) r * z = 1) : r • multiply R P s a z = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  change r • (z * (show (⋀[R]^n (KoszulPartial.Fractions.normal R (c := c))) →ₗ[R] P.obj a from φ) x) = _
  rw [Algebra.smul_def, ← mul_assoc, hz, one_mul]
  rfl

def sourceNull (j : Fin m) : Homotopy (t j • 𝟙 (KoszulPartial.Components.source R s t)) 0 := by
  let e : KoszulPartial.Fractions.ambient R (c := c) (m := m) := (0, Pi.basisFun R (Fin m) j)
  have he : KoszulPartial.Differential.equation R s t e = t j := by
    simp [KoszulPartial.Differential.equation, e, GeneratorMatrix.equation_apply, Pi.basisFun_apply, Pi.single_apply]
  exact (Homotopy.ofEq (by rw [← he])).trans
    (CentralNullHomotopy.dual R _ _
      (Exterior.KoszulHomotopy.homotopy R _ (KoszulPartial.Differential.equation R s t) e))

def mapsNull (a : Cᵒᵖ) (j : Fin m)
    (hj : IsUnit (algebraMap R (P.obj a) (t j)))
    (f : KoszulPartial.Components.source R s t ⟶ coefficientAt R P s a) : Homotopy f 0 :=
  CentralNullHomotopy.of_inverse R (t j) (sourceNull R s t j)
    (multiply R P s a (↑(hj.unit⁻¹)))
    (multiply_inverse R P s a (t j) (↑(hj.unit⁻¹)) (by
      exact (congrArg (fun z : P.obj a => z * ↑(hj.unit⁻¹)) hj.unit_spec.symm).trans
        (Units.mul_inv hj.unit))) f

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.PuncturedHomotopy
