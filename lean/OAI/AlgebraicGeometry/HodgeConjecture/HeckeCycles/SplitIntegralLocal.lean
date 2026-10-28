import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SplitIntegralCoefficients
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.IntegralSquares
import OAI.RepresentationTheory.Theta.Adelic.IntegralTopology
import OAI.RepresentationTheory.Weil.AdelicSplitting.Assembly

/-! # Split Integral Local -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SplitIntegralLocal.CM

noncomputable section

/-! Outside finitely many finite places, an integral first split matrix
and its inverse reconstruct an integral local special-unitary matrix. -/

open scoped Classical _root_.NumberField
open Filter OAI.RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra OAI.RepresentationTheory.Theta.Adelic.SplitUnitary

variable (F : Type) [Field F] [NumberField F] {n : ℕ} {d : F}
  (H : (Matrix (Fin n) (Fin n) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)

def Good (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : Prop :=
  RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) (2 : F)⁻¹ ∈ RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) ∧
  RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d ∈ RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) ∧
  RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d⁻¹ ∈ RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) ∧
  ∀ i j, ((RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H (.inr v)).val i j).re ∈ RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) ∧
    ((RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H (.inr v)).val i j).im ∈ RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) ∧
    ((RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H (.inr v)).inv i j).re ∈ RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) ∧
    ((RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H (.inr v)).inv i j).im ∈ RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v)

theorem cofinite : ∀ᶠ v in Filter.cofinite, Good F H v := by
  have hs (x : F) : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) x ∈ RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) :=
    Sum.inr_injective.tendsto_cofinite.eventually (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalScalar_integral F x)
  have hm : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i j, RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) (H.val i j).re ∈ RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) ∧
        RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) (H.val i j).im ∈ RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) ∧
        RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) (H.inv i j).re ∈ RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) ∧
        RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) (H.inv i j).im ∈ RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
      (hs (H.val i j).re).and ((hs (H.val i j).im).and
        ((hs (H.inv i j).re).and (hs (H.inv i j).im)))
  filter_upwards [hs (2 : F)⁻¹, hs d, hs d⁻¹, hm] with v h2 hd hdi hm
  exact ⟨h2, hd, hdi, hm⟩

variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))

local instance : CharZero (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) := RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.completionCharZero F (.inr v)

theorem integral (hgood : Good F H v)
    (r : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) (hr : r ^ 2 = RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d) (hr0 : r ≠ 0)
    (hH : (RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H (.inr v)).val.conjTranspose = (RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H (.inr v)).val)
    (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v)))
    (hg : ∀ i j, RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra.plus r hr hr0 (g.val.val i j) ∈ RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v))
    (hgi : ∀ i j, RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra.plus r hr hr0 ((g⁻¹).val.val i j) ∈ RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v)) :
    g ∈ RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F H.val (.inr v) := by
  let S := RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v)
  have hrS : r ∈ S := Local.IntegralSquares.CM.of_square F v r (hr ▸ hgood.2.1)
  have hiS : r⁻¹ ∈ S := Local.IntegralSquares.CM.inverse_of_square F v r hr hgood.2.2.1
  have h2S : (2 : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v))⁻¹ ∈ S := by
    simpa only [map_inv₀, map_ofNat] using hgood.1
  have h2rS : (2 * r)⁻¹ ∈ S := by
    rw [mul_inv_rev]
    exact S.mul_mem hiS h2S
  have hp : ∀ i j, (RepresentationTheory.Theta.Adelic.SplitUnitary.plusUnits r hr hr0 (RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H (.inr v))).val i j ∈ S := by
    intro i j
    exact S.add_mem (hgood.2.2.2 i j).1 (S.mul_mem hrS (hgood.2.2.2 i j).2.1)
  have hpi : ∀ i j, (RepresentationTheory.Theta.Adelic.SplitUnitary.plusUnits r hr hr0 (RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H (.inr v)))⁻¹.val i j ∈ S := by
    intro i j
    exact S.add_mem (hgood.2.2.2 i j).2.2.1 (S.mul_mem hrS (hgood.2.2.2 i j).2.2.2)
  have hc := SplitIntegralCoefficients.CM.special_unitary_coefficients
    r hr hr0 S h2S h2rS (RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H (.inr v)) hH hp hpi g hg hgi
  have hci := SplitIntegralCoefficients.CM.special_unitary_coefficients
    r hr hr0 S h2S h2rS (RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H (.inr v)) hH hp hpi g⁻¹ hgi
      (fun i j => Eq.mpr (congrArg (fun u : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v)) =>
        RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra.plus r hr hr0 (u.val.val i j) ∈ S) (inv_inv g)) (hg i j))
  exact ⟨fun i j => RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.quadraticOrder_of_coeff F d (.inr v) _ (hc i j).1 (hc i j).2,
    fun i j => RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.quadraticOrder_of_coeff F d (.inr v) _ (hci i j).1 (hci i j).2⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SplitIntegralLocal.CM
