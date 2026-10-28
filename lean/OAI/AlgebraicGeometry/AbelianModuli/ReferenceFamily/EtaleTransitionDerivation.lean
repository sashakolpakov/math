import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.Derivation
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.EtaleDerivation

/-! # Etale Transition Derivation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleTransitionDerivation

noncomputable section

section

/-! Transition derivations extend uniquely to etale coordinate rings,
including localizations; their dual-number gauges retain the restriction square. -/

open scoped TensorProduct

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [Algebra.FormallyEtale A B]

def etaleTransitionDerivation (d : Derivation k A A) : Derivation k B B :=
  HodgeConjecture.DegreeTwo.EtaleDerivation.Constructions.etaleExtendDerivation k A B B ((Algebra.linearMap A B).compDer d)

theorem etaleTransitionDerivation_algebraMap (d : Derivation k A A) (a : A) :
    etaleTransitionDerivation (B := B) d (algebraMap A B a) = algebraMap A B (d a) :=
  HodgeConjecture.DegreeTwo.EtaleDerivation.Constructions.etaleExtendDerivation_algebraMap k A B B
    ((Algebra.linearMap A B).compDer d) a

theorem etaleTransitionDerivation_ext (d e : Derivation k B B)
    (h : ∀ a : A, d (algebraMap A B a) = e (algebraMap A B a)) : d = e := by
  have hd : d.liftKaehlerDifferential = e.liftKaehlerDifferential := by
    apply (KaehlerDifferential.isBaseChange_of_formallyEtale k A B).algHom_ext'
    apply Derivation.liftKaehlerDifferential_unique
    apply Derivation.ext
    intro a
    change d.liftKaehlerDifferential
        (KaehlerDifferential.map k k A B (KaehlerDifferential.D k A a)) =
      e.liftKaehlerDifferential
        (KaehlerDifferential.map k k A B (KaehlerDifferential.D k A a))
    rw [KaehlerDifferential.map_D, Derivation.liftKaehlerDifferential_comp_D,
      Derivation.liftKaehlerDifferential_comp_D]
    exact h a
  apply Derivation.ext
  intro b
  rw [← Derivation.liftKaehlerDifferential_comp_D d b,
    ← Derivation.liftKaehlerDifferential_comp_D e b, hd]

theorem etaleTransitionDerivation_unique (d : Derivation k A A) (e : Derivation k B B)
    (h : ∀ a : A, e (algebraMap A B a) = algebraMap A B (d a)) :
    e = etaleTransitionDerivation d := by
  apply etaleTransitionDerivation_ext (A := A)
  intro a
  exact (h a).trans (etaleTransitionDerivation_algebraMap d a).symm

theorem etaleTransitionDerivation_gauge_natural (d : Derivation k A A) :
    (Dual.NumberCoefficients.dualNumberAlgMap (IsScalarTower.toAlgHom k A B)).comp
        (Dual.Derivation.dualDerivationAutomorphism d).toAlgHom =
      (Dual.Derivation.dualDerivationAutomorphism (etaleTransitionDerivation (B := B) d)).toAlgHom.comp
        (Dual.NumberCoefficients.dualNumberAlgMap (IsScalarTower.toAlgHom k A B)) :=
  Dual.Derivation.dualDerivationAutomorphism_natural (IsScalarTower.toAlgHom k A B) d
    (etaleTransitionDerivation d) (fun a => (etaleTransitionDerivation_algebraMap d a).symm)

end

/-! Restriction of transition derivations is linear and composes exactly
along etale coordinate changes, so it preserves cocycles and coboundaries. -/

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [Algebra.FormallyEtale A B]

theorem etaleTransitionDerivation_add (d e : Derivation k A A) :
    etaleTransitionDerivation (B := B) (d + e) =
      etaleTransitionDerivation d + etaleTransitionDerivation e := by
  apply etaleTransitionDerivation_ext (A := A)
  intro a
  simp only [etaleTransitionDerivation_algebraMap, Derivation.add_apply, map_add]

theorem etaleTransitionDerivation_smul (c : k) (d : Derivation k A A) :
    etaleTransitionDerivation (B := B) (c • d) = c • etaleTransitionDerivation d := by
  apply etaleTransitionDerivation_ext (A := A)
  intro a
  simp only [etaleTransitionDerivation_algebraMap, Derivation.smul_apply]
  exact (IsScalarTower.toAlgHom k A B).toLinearMap.map_smul c (d a)

def etaleTransitionDerivationLinear : Derivation k A A →ₗ[k] Derivation k B B where
  toFun := etaleTransitionDerivation
  map_add' := etaleTransitionDerivation_add
  map_smul' := etaleTransitionDerivation_smul

variable {C : Type*} [CommRing C] [Algebra k C] [Algebra A C] [Algebra B C]
    [IsScalarTower k A C] [IsScalarTower k B C] [IsScalarTower A B C]
    [Algebra.FormallyEtale B C] [Algebra.FormallyEtale A C]

theorem etaleTransitionDerivation_tower (d : Derivation k A A) :
    etaleTransitionDerivation (B := C) d =
      etaleTransitionDerivation (B := C) (etaleTransitionDerivation (B := B) d) := by
  apply etaleTransitionDerivation_ext (A := A)
  intro a
  rw [etaleTransitionDerivation_algebraMap, IsScalarTower.algebraMap_apply A B C a,
    etaleTransitionDerivation_algebraMap, etaleTransitionDerivation_algebraMap,
    ← IsScalarTower.algebraMap_apply A B C]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleTransitionDerivation
