import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Localization.Algebra

/-! # Localized Extension Kernel -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedExtensionKernel

noncomputable section

/-! An actual localization of an extension, with its extended kernel,
satisfies the native kernel base-change hypothesis automatically. -/

open _root_.Algebra.Extension

set_option backward.isDefEq.respectTransparency false

universe u
variable {k S T : Type u} [CommRing k] [CommRing S] [CommRing T]
  [Algebra k S] [Algebra k T] [Algebra S T]
  (P : Algebra.Extension.{u} k S) (Q : Algebra.Extension.{u} k T) (f : P.Hom Q)
  [Algebra P.Ring Q.Ring] (halg : algebraMap P.Ring Q.Ring = f.toRingHom)
  (M : Submonoid P.Ring) [IsLocalization M Q.Ring]
  (hker : P.ker.map (algebraMap P.Ring Q.Ring) = Q.ker)

include hker in
theorem isLocalizedModule : IsLocalizedModule M (f.mapKer halg) := by
  let e : (P.ker.map (algebraMap P.Ring Q.Ring)) ≃ₗ[P.Ring] Q.ker :=
    (LinearEquiv.ofEq _ _ hker).restrictScalars P.Ring
  have he : f.mapKer halg = e.toLinearMap.comp (Algebra.idealMap P.ker (S := Q.Ring)) := by
    ext x
    exact (RingHom.congr_fun halg x.val).symm
  rw [he]
  exact IsLocalizedModule.of_linearEquiv M (Algebra.idealMap P.ker (S := Q.Ring)) e

include M hker in
theorem kernel_bijective : Function.Bijective ((f.mapKer halg).liftBaseChange Q.Ring) :=
  (isLocalizedModule_iff_isBaseChange M Q.Ring (f.mapKer halg)).mp
    (isLocalizedModule P Q f halg M hker)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedExtensionKernel
