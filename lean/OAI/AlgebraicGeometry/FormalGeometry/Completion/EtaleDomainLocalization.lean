import OAI.AlgebraicGeometry.FormalGeometry.Completion.SmoothIntegralClosure
import OAI.AlgebraicGeometry.FormalGeometry.Completion.LocalIntegralClosureDomain
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.LocalProperties.Reduced

/-! # Etale Domain Localization -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.EtaleDomainLocalization.Construction

noncomputable section

/-!
# Completion: local domains in étale charts over a normal domain

Smooth base change and localization preserve integral closedness in the
generic algebra. That algebra is reduced Artinian, so its local integral
closures are domains. No regular-local-ring theorem is assumed.
-/

open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w

variable (R : Type u) (K : Type v) (S : Type w)
  [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing S] [Algebra R S] [Algebra.Etale R S]

include R K

omit [IsDomain R] in
/-- Every prime localization of an étale algebra over an integrally closed domain is a domain. -/
theorem etale_localization_isNormalDomain (q : Ideal S) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let G := S ⊗[R] K
  let T := Localization.AtPrime q
  have : IsIntegrallyClosedIn R K :=
    (isIntegrallyClosed_iff_isIntegralClosure K).mp inferInstance
  have : IsIntegrallyClosedIn S G := SmoothIntegralClosure.Construction.smooth_integrallyClosedIn_baseChange R S K
  have : IsIntegrallyClosedIn T (T ⊗[S] G) :=
    SmoothIntegralClosure.Construction.localization_integrallyClosedIn_baseChange S T G q.primeCompl
  let : Algebra K G := Algebra.TensorProduct.rightAlgebra
  have : Algebra.Etale K G := Algebra.Etale.of_equiv (Algebra.TensorProduct.commRight R K S)
  have : Module.Finite K G := Algebra.FormallyUnramified.finite_of_free K G
  have : IsArtinianRing G := IsArtinianRing.of_finite K G
  have : IsReduced G := Algebra.FormallyUnramified.isReduced_of_field K G
  let : Algebra G (T ⊗[S] G) := Algebra.TensorProduct.rightAlgebra
  let M := Algebra.algebraMapSubmonoid G q.primeCompl
  have : IsLocalization M (T ⊗[S] G) := IsLocalization.tensorRight T q.primeCompl
  have : IsArtinianRing (T ⊗[S] G) := IsArtinianRing.localization_artinian M _
  have : IsReduced (T ⊗[S] G) := isReduced_localizationPreserves M _ inferInstance
  exact ⟨LocalIntegralClosureDomain.Construction.local_integrallyClosedIn_artinian_isDomain T (T ⊗[S] G),
    LocalIntegralClosureDomain.Construction.local_integrallyClosedIn_artinian_isIntegrallyClosed T (T ⊗[S] G)⟩

omit [IsDomain R] in
/-- Every prime localization of an étale algebra over an integrally closed domain is a domain. -/
theorem etale_localization_isDomain (q : Ideal S) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) := (etale_localization_isNormalDomain R K S q).1

omit [IsDomain R] in
/-- Every prime localization of an étale algebra over a normal domain is integrally closed. -/
theorem etale_localization_isIntegrallyClosed (q : Ideal S) [q.IsPrime] :
    IsIntegrallyClosed (Localization.AtPrime q) := (etale_localization_isNormalDomain R K S q).2

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.EtaleDomainLocalization.Construction
