import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PiExtension

/-! # Pi Extension Iterated -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.PiExtensionIterated

noncomputable section

/-! Scalar-extension comparisons in curried pair and triple coordinates. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory

universe u

namespace Construction.FinitePiExtension

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
variable {I J L : Type u} [Finite I] [Finite J] [Finite L]

def data2 (P : I → J → ModuleCat.{u} R) (Q : I → J → ModuleCat.{u} S)
    (v : ∀ i j, P i j → Q i j) (d : ∀ i j, NormalizedScalar.Construction.NormalizedScalarIso.Data f (v i j)) :
    NormalizedScalar.Construction.NormalizedScalarIso.Data f (B := ModuleCat.of S (∀ i j, Q i j))
      (fun s : ModuleCat.of R (∀ i j, P i j) => fun i j => v i j (s i j)) :=
  PiExtension.Construction.FinitePiExtension.data f (fun i => ModuleCat.of R (∀ j, P i j)) (fun i => ModuleCat.of S (∀ j, Q i j))
    (fun i s j => v i j (s j)) (fun i => PiExtension.Construction.FinitePiExtension.data f (P i) (Q i) (v i) (d i))

def data3 (P : I → J → L → ModuleCat.{u} R) (Q : I → J → L → ModuleCat.{u} S)
    (v : ∀ i j k, P i j k → Q i j k) (d : ∀ i j k, NormalizedScalar.Construction.NormalizedScalarIso.Data f (v i j k)) :
    NormalizedScalar.Construction.NormalizedScalarIso.Data f (B := ModuleCat.of S (∀ i j k, Q i j k))
      (fun s : ModuleCat.of R (∀ i j k, P i j k) => fun i j k => v i j k (s i j k)) :=
  PiExtension.Construction.FinitePiExtension.data f (fun i => ModuleCat.of R (∀ j k, P i j k)) (fun i => ModuleCat.of S (∀ j k, Q i j k))
    (fun i s j k => v i j k (s j k)) (fun i => data2 f (P i) (Q i) (v i) (d i))

end Construction.FinitePiExtension

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.PiExtensionIterated
