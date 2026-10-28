import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IdealModule
import OAI.AlgebraicGeometry.Divisors.LineBundles.RegularPrincipalGenerator

/-! # Ideal Equation Frame -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IdealEquationFrame.BundleCycles

noncomputable section

/-! A regular equation for the actual section kernel gives
a genuine linear frame of the ideal's module of sections. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Z : Scheme.{0}} (i : Z ⟶ X) (U : X.Opens) (t : Γ(X, U))
    (ht : IsRegular t) (hk : RingHom.ker (i.app U).hom = Ideal.span {t})

def schemeIdealEquationSection : Γ(SchemeIdealModule.BundleCycles.schemeIdealModule i, U) :=
  (IdealModule.BundleCycles.schemeIdealModuleSectionsIso i U).inv ⟨t, hk.symm ▸ Ideal.subset_span (Set.mem_singleton t)⟩

theorem schemeIdealEquationSection_image :
    IdealModule.BundleCycles.schemeIdealModuleSectionLinear i U (schemeIdealEquationSection i U t hk) = t :=
  (IdealModule.BundleCycles.schemeIdealModuleSectionLinear_apply i U _).trans (IdealModule.BundleCycles.schemeIdealModuleSectionsIso_inv_apply i U _)

def schemeIdealEquationFrame : Γ(SchemeIdealModule.BundleCycles.schemeIdealModule i, U) ≃ₗ[Γ(X, U)] Γ(X, U) := by
  let s := schemeIdealEquationSection i U t hk
  have hs : IdealModule.BundleCycles.schemeIdealModuleSectionLinear i U s = t := schemeIdealEquationSection_image i U t hk
  exact (RegularPrincipalGenerator.BundleCycles.regularPrincipalGeneratorEquiv (IdealModule.BundleCycles.schemeIdealModuleSectionLinear i U)
    (IdealModule.BundleCycles.schemeIdealModuleSectionLinear_injective i U) s (hs.symm ▸ ht)
    (fun m => by rw [hs, ← hk]; exact IdealModule.BundleCycles.schemeIdealModuleSectionLinear_mem i U m)).symm

theorem schemeIdealEquationFrame_image (m : Γ(SchemeIdealModule.BundleCycles.schemeIdealModule i, U)) :
    IdealModule.BundleCycles.schemeIdealModuleSectionLinear i U m = schemeIdealEquationFrame i U t ht hk m * t := by
  let e := schemeIdealEquationFrame i U t ht hk
  have h : m = e m • schemeIdealEquationSection i U t hk := (e.symm_apply_apply m).symm
  calc
    IdealModule.BundleCycles.schemeIdealModuleSectionLinear i U m =
        IdealModule.BundleCycles.schemeIdealModuleSectionLinear i U (e m • schemeIdealEquationSection i U t hk) :=
      congrArg (IdealModule.BundleCycles.schemeIdealModuleSectionLinear i U) h
    _ = e m * t := by rw [map_smul, schemeIdealEquationSection_image]; rfl

theorem schemeIdealModuleSectionLinear_restrict {X Z : Scheme.{0}}
    (i : Z ⟶ X) {U V : X.Opens} (h : V ≤ U) (m : Γ(SchemeIdealModule.BundleCycles.schemeIdealModule i, U)) :
    IdealModule.BundleCycles.schemeIdealModuleSectionLinear i V ((SchemeIdealModule.BundleCycles.schemeIdealModule i).presheaf.map (homOfLE h).op m) =
      X.presheaf.map (homOfLE h).op (IdealModule.BundleCycles.schemeIdealModuleSectionLinear i U m) :=
  (IdealModule.BundleCycles.schemeIdealModuleSectionLinear_apply i V _).trans ((IdealModule.BundleCycles.schemeIdealModuleInclusion_restrict i h m).trans
    (congrArg (X.presheaf.map (homOfLE h).op) (IdealModule.BundleCycles.schemeIdealModuleSectionLinear_apply i U m).symm))

theorem schemeIdealEquationFrame_restrict {X Z : Scheme.{0}} (i : Z ⟶ X)
    (U V : X.Opens) (h : U ≤ V) (tU : Γ(X, U)) (tV : Γ(X, V))
    (htU : IsRegular tU) (htV : IsRegular tV)
    (hkU : RingHom.ker (i.app U).hom = Ideal.span {tU})
    (hkV : RingHom.ker (i.app V).hom = Ideal.span {tV}) (m : Γ(SchemeIdealModule.BundleCycles.schemeIdealModule i, V)) :
    schemeIdealEquationFrame i U tU htU hkU ((SchemeIdealModule.BundleCycles.schemeIdealModule i).presheaf.map (homOfLE h).op m) * tU =
      X.presheaf.map (homOfLE h).op (schemeIdealEquationFrame i V tV htV hkV m) *
        X.presheaf.map (homOfLE h).op tV := by
  rw [← schemeIdealEquationFrame_image, schemeIdealModuleSectionLinear_restrict,
    schemeIdealEquationFrame_image i V tV htV hkV, map_mul]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IdealEquationFrame.BundleCycles
