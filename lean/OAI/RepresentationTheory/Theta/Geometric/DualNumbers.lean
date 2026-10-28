import OAI.RepresentationTheory.Theta.Geometric.DerivationBaseChange

/-! # Dual Numbers -/

namespace OAI.RepresentationTheory.Theta.Geometric.DualNumbers

noncomputable section

/-! Infinitesimal points over an extended residue field are actual algebra
maps to that field's dual numbers. -/

variable {k A F : Type} [Field k] [CommRing A] [Field F]
  [Algebra k A] [Algebra k F] [Algebra A F] [IsScalarTower k A F]

def geometricDerivationJet (δ : Derivation k A F) : A →ₐ[k] DualNumber F where
  toFun a := (algebraMap A F a, δ a)
  map_zero' := by
    apply TrivSqZeroExt.ext
    · exact map_zero (algebraMap A F)
    · exact map_zero δ
  map_one' := by
    apply TrivSqZeroExt.ext
    · exact map_one (algebraMap A F)
    · exact δ.map_one_eq_zero
  map_add' a b := by
    apply TrivSqZeroExt.ext
    · exact map_add (algebraMap A F) a b
    · exact map_add δ a b
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · exact map_mul (algebraMap A F) a b
    · change δ (a * b) = algebraMap A F a * δ b + δ a * algebraMap A F b
      simpa only [Algebra.smul_def, mul_comm] using δ.leibniz a b
  commutes' c := by
    apply TrivSqZeroExt.ext
    · exact (IsScalarTower.algebraMap_apply k A F c).symm
    · exact δ.map_algebraMap c

def geometricJetDerivation
    (f : {f : A →ₐ[k] DualNumber F // ∀ a, (f a).fst = algebraMap A F a}) :
    Derivation k A F where
  toFun a := (f.val a).snd
  map_add' a b := by rw [map_add, TrivSqZeroExt.snd_add]
  map_smul' c a := by rw [map_smul, TrivSqZeroExt.snd_smul]; rfl
  map_one_eq_zero' := by
    change (f.val 1).snd = 0
    rw [map_one]; rfl
  leibniz' a b := by
    change (f.val (a * b)).snd = a • (f.val b).snd + b • (f.val a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, f.property a, f.property b]
    simp [Algebra.smul_def, add_comm, mul_comm]

@[simp] theorem geometricDerivationJet_fst (δ : Derivation k A F) (a : A) :
    (geometricDerivationJet δ a).fst = algebraMap A F a := rfl

@[simp] theorem geometricDerivationJet_snd (δ : Derivation k A F) (a : A) :
    (geometricDerivationJet δ a).snd = δ a := rfl

def geometricDerivationJetEquiv : Derivation k A F ≃
    {f : A →ₐ[k] DualNumber F // ∀ a, (f a).fst = algebraMap A F a} where
  toFun δ := ⟨geometricDerivationJet δ, fun _ => rfl⟩
  invFun := geometricJetDerivation
  left_inv δ := by apply Derivation.ext; intro a; rfl
  right_inv f := by
    apply Subtype.ext
    apply AlgHom.ext
    intro a
    apply TrivSqZeroExt.ext
    · exact (f.property a).symm
    · rfl

theorem geometricDerivationJet_add_snd (δ ε : Derivation k A F) (a : A) :
    (geometricDerivationJet (δ + ε) a).snd =
      (geometricDerivationJet δ a).snd + (geometricDerivationJet ε a).snd := rfl

theorem geometricDerivationJet_smul_snd (c : F) (δ : Derivation k A F) (a : A) :
    (geometricDerivationJet (c • δ) a).snd = c * (geometricDerivationJet δ a).snd := rfl

end

end OAI.RepresentationTheory.Theta.Geometric.DualNumbers
