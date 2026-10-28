import OAI.RepresentationTheory.Theta.Adelic.LocalIntegralFactorization
import OAI.RepresentationTheory.Theta.Adelic.IntegralOpenCellVacuum
import OAI.RepresentationTheory.Theta.Adelic.IntegralTensor

/-! # All Integral Vacuum -/

namespace OAI.RepresentationTheory.Theta.Adelic.AllIntegralVacuum

noncomputable section

/-! Exact preservation of the standard finite vacuum by the entire
integral unitary pair group, using the checked normalization and finite
integral open-cell factorization. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.GlobalFrameIntegral OAI.RepresentationTheory.Theta.Adelic.IntegralScalarFamily.Family OAI.RepresentationTheory.Theta.Adelic.LocalIntegralFactorization
open OAI.RepresentationTheory.Theta.Adelic.UnramifiedPlace.Data OAI.RepresentationTheory.Theta.Adelic.IntegralOpenCellVacuum

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0) (hns : ¬ IsSquare d) (n m : ℕ)
variable (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d n m H K) (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d n m)
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
local instance : MeasurableSpace (v.adicCompletion F) := borel (v.adicCompletion F)
local instance : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
variable (hv : UnramifiedPlace.Data.UnramifiedPlaceData F d n m C v)
variable (hP : GlobalFrameIntegral.IntegralFrameAt F d n m H K P (.inr v))
variable (hz : IntegralScalarFamily.Family.IntegralScalarFamilyAt F d hns (2 * (n + m) + 1) (.inr v))
variable (hH : (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H (.inr v)).val.conjTranspose = (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H (.inr v)).val)
variable (hK : (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d K (.inr v)).val.conjTranspose = -(Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d K (.inr v)).val)
variable (hHI : ∀ i j, (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H (.inr v)).val i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v))
variable (hHi : ∀ i j, (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H (.inr v)).inv i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v))
variable (hKI : ∀ i j, (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d K (.inr v)).val i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v))
variable (hKi : ∀ i j, (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d K (.inr v)).inv i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v))
variable (s : (Weil.AdelicSplitting.Integral.Construction.LocalUnitary F H.val (.inr v) × Weil.AdelicSplitting.Integral.Construction.LocalUnitary F K.val (.inr v)) →ₜ* Weil.AdelicSplitting.Vacuum.Construction.CoverAt F (n * m) C.ψ (.inr v))
variable (hs : Weil.AdelicSplitting.CorrectedNormalization.Construction.CorrectedLocalNormalization F d hd n m C (.inr v)
  (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H (.inr v)) (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d K (.inr v)) (P.localFrame (.inr v)) s)

include hv hP hz hK hHI hHi hKI hKi hs in
theorem first_integral_fixes_vacuum
    (x : Weil.AdelicSplitting.Integral.Construction.LocalUnitary F H.val (.inr v))
    (hx : ∀ i j, x.val.val i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v)) :
    Weil.AdelicSplitting.Oscillator.Construction.localOperator (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m) (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
      (s (x, 1)) (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m) v) = Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m) v := by
  let U := (Weil.AdelicSplitting.Oscillator.Construction.vacuumStabilizer (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m)
    (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inr v)) (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m) v)).comap
      (s.toMonoidHom.comp (MonoidHom.inl _ _))
  change x ∈ U
  apply LocalIntegralFactorization.OpenGeneration.integral_unitary_mem_of_open F d hns v hv.parameter_integral
    (2 * (n + m) + 1) n (by omega) hz (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H (.inr v)).val U _ x hx
  intro y hy
  obtain ⟨u, hu, hui, hui'⟩ := hy
  exact IntegralOpenCellVacuum.first_openCell_fixes_vacuum F d hd n m H K P C v hv hP hHI hHi hKI hKi s hs hK y u hu hui hui'

include hv hP hz hH hHI hHi hKI hKi hs in
theorem second_integral_fixes_vacuum
    (x : Weil.AdelicSplitting.Integral.Construction.LocalUnitary F K.val (.inr v))
    (hx : ∀ i j, x.val.val i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v)) :
    Weil.AdelicSplitting.Oscillator.Construction.localOperator (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m) (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
      (s (1, x)) (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m) v) = Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m) v := by
  let U := (Weil.AdelicSplitting.Oscillator.Construction.vacuumStabilizer (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m)
    (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inr v)) (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m) v)).comap
      (s.toMonoidHom.comp (MonoidHom.inr _ _))
  change x ∈ U
  apply LocalIntegralFactorization.OpenGeneration.integral_unitary_mem_of_open F d hns v hv.parameter_integral
    (2 * (n + m) + 1) m (by omega) hz (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d K (.inr v)).val U _ x hx
  intro y hy
  obtain ⟨u, hu, hui, hui'⟩ := hy
  exact IntegralOpenCellVacuum.second_openCell_fixes_vacuum F d hd n m H K P C v hv hP hHI hHi hKI hKi s hs hH y u hu hui hui'

include hv hP hz hH hK hHI hHi hKI hKi hs in
theorem integral_pair_fixes_vacuum
    (g : Weil.AdelicSplitting.Integral.Construction.LocalUnitary F H.val (.inr v) × Weil.AdelicSplitting.Integral.Construction.LocalUnitary F K.val (.inr v))
    (hg : g ∈ Weil.AdelicSplitting.Integral.Construction.localPairIntegral F H.val K.val (.inr v)) :
    Weil.AdelicSplitting.Oscillator.Construction.localOperator (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m) (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
      (s g) (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m) v) = Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m) v := by
  let U := (Weil.AdelicSplitting.Oscillator.Construction.vacuumStabilizer (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m)
    (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inr v)) (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m) v)).comap s.toMonoidHom
  change g ∈ U
  have hfa : (g.1, 1) ∈ U :=
    first_integral_fixes_vacuum F d hd hns n m H K P C v hv hP hz hK hHI hHi hKI hKi s hs g.1 hg.1.1
  have hfb : (1, g.2) ∈ U :=
    second_integral_fixes_vacuum F d hd hns n m H K P C v hv hP hz hH hHI hHi hKI hKi s hs g.2 hg.2.1
  have hpair : g = (g.1, 1) * (1, g.2) := Prod.ext (mul_one g.1).symm (one_mul g.2).symm
  rw [hpair]
  exact U.mul_mem hfa hfb

end

end OAI.RepresentationTheory.Theta.Adelic.AllIntegralVacuum
