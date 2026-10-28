import OAI.RepresentationTheory.Theta.Adelic.UniformUnramifiedSplitting
import OAI.RepresentationTheory.Theta.Adelic.AllPlacesLocalSplitting

/-! # Construct Normalized Splittings -/

namespace OAI.RepresentationTheory.Theta.Adelic.ConstructNormalizedSplittings

noncomputable section

/-! Existence of the complete normalized local splitting family,
including the uniform unramified condition needed for adelic assembly. -/

open OAI.RepresentationTheory.Theta.Adelic.UniformUnramifiedSplitting

theorem exists_normalized_local_splittings
    (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0) (hns : ¬ IsSquare d)
    (n m : ℕ) (hnm : 0 < n * m)
    (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d n m) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d n m H K) :
    Nonempty (Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P) := by
  have he (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) := AllPlacesLocalSplitting.normalized_splitting_at_every_place
    F d hd C v hnm (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H v) (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d K v)
    (UniformUnramifiedSplitting.localized_hermitian F d n H hH v) (UniformUnramifiedSplitting.localized_skew F d m K hK v) (P.localFrame v)
  let s := fun v => (he v).choose
  have hc (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) (g : Weil.AdelicSplitting.Integral.Construction.LocalUnitary F H.val v × Weil.AdelicSplitting.Integral.Construction.LocalUnitary F K.val v) :
      Weil.AdelicSplitting.Vacuum.Construction.projectionAt F (n * m) C.ψ v (s v g) = Weil.AdelicSplitting.Assembly.Construction.localDualAction F d n m H K P v g := (he v).choose_spec.1 g
  have hn (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) : Weil.AdelicSplitting.CorrectedNormalization.Construction.CorrectedLocalNormalization F d hd n m C v
      (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H v) (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d K v) (P.localFrame v) (s v) := (he v).choose_spec.2
  exact ⟨{
    atPlace := s
    covers := hc
    normalization := hn
    unramified := UniformUnramifiedSplitting.normalized_family_unramified F d hd hns n m H K hH hK C P s hc hn }⟩

end

end OAI.RepresentationTheory.Theta.Adelic.ConstructNormalizedSplittings
