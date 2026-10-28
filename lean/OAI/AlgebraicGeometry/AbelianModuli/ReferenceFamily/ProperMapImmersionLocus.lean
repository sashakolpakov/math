import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FiberwiseOpenLocus
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Proper Map Immersion Locus -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProperMapImmersionLocus

noncomputable section

section

/-! An actual proper scheme family has a universal open base locus
where a given morphism factors through a specified open subscheme.
The criterion holds after every actual scheme base change. For an
open family map and a clopen target condition the locus is clopen. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X S : Scheme.{0}} (p : X ⟶ S) [IsProper p] (U : X.Opens)

def schemeFiberwiseOpenLocus : S.Opens := FiberwiseOpenLocus.fiberwiseOpenLocus p p.isClosedMap U

theorem schemeFiberwiseOpenLocus_baseChange
    {Z T : Scheme.{0}} (a : Z ⟶ X) (b : Z ⟶ T) (q : T ⟶ S)
    (h : IsPullback a b p q) :
    Set.range q ⊆ schemeFiberwiseOpenLocus p U ↔ ∀ z, a z ∈ U :=
  FiberwiseOpenLocus.fiberwiseOpenLocus_baseChange p p.isClosedMap U a b q
    (fun z => congrArg (fun m : Z ⟶ S => m z) h.w)
    (Scheme.exists_preimage_of_isPullback h)

variable {Y : Scheme.{0}} (f : X ⟶ Y) (V : Y.Opens)

def properMapOpenLocus : S.Opens := schemeFiberwiseOpenLocus p (f ⁻¹ᵁ V)

theorem properMapOpenLocus_isClosed (hp : IsOpenMap p) (hV : IsClosed (V : Set Y)) :
    IsClosed (properMapOpenLocus p f V : Set S) :=
  FiberwiseOpenLocus.fiberwiseOpenLocus_isClosed p p.isClosedMap (f ⁻¹ᵁ V) hp (hV.preimage f.continuous)

theorem properMapOpenLocus_baseChange_factor
    {Z T : Scheme.{0}} (a : Z ⟶ X) (b : Z ⟶ T) (q : T ⟶ S)
    (h : IsPullback a b p q) :
    Set.range q ⊆ properMapOpenLocus p f V ↔
      ∃! k : Z ⟶ V.toScheme, k ≫ V.ι = a ≫ f := by
  refine (schemeFiberwiseOpenLocus_baseChange p (f ⁻¹ᵁ V) a b q h).trans ?_
  constructor
  · intro hz
    have hr : Set.range (a ≫ f) ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      exact hz z
    let k := IsOpenImmersion.lift V.ι (a ≫ f) hr
    have hk : k ≫ V.ι = a ≫ f := IsOpenImmersion.lift_fac _ _ _
    refine ⟨k, hk, ?_⟩
    intro l hl
    exact (cancel_mono V.ι).mp (hl.trans hk.symm)
  · rintro ⟨k, hk, _⟩ z
    change (a ≫ f) z ∈ V
    rw [← hk]
    exact (k z).property

end

/-! The proper-family open locus classifies factorization through an
actual open immersion. A closed immersion gives a clopen condition
when the family map is open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X S Y H : Scheme.{0}} (p : X ⟶ S) [IsProper p]
    (f : X ⟶ Y) (j : H ⟶ Y) [IsOpenImmersion j]

def properMapImmersionLocus : S.Opens :=
  properMapOpenLocus p f ⟨Set.range j, j.isOpenEmbedding.isOpen_range⟩

theorem properMapImmersionLocus_isClosed [IsClosedImmersion j]
    (hp : IsOpenMap p) : IsClosed (properMapImmersionLocus p f j : Set S) :=
  properMapOpenLocus_isClosed p f
    ⟨Set.range j, j.isOpenEmbedding.isOpen_range⟩ hp j.isClosedMap.isClosed_range

theorem properMapImmersionLocus_baseChange_factor
    {Z T : Scheme.{0}} (a : Z ⟶ X) (b : Z ⟶ T) (q : T ⟶ S)
    (h : IsPullback a b p q) :
    Set.range q ⊆ properMapImmersionLocus p f j ↔
      ∃! k : Z ⟶ H, k ≫ j = a ≫ f := by
  refine (schemeFiberwiseOpenLocus_baseChange p
    (f ⁻¹ᵁ ⟨Set.range j, j.isOpenEmbedding.isOpen_range⟩) a b q h).trans ?_
  constructor
  · intro hz
    have hr : Set.range (a ≫ f) ⊆ Set.range j := by
      rintro _ ⟨z, rfl⟩
      exact hz z
    let k := IsOpenImmersion.lift j (a ≫ f) hr
    have hk : k ≫ j = a ≫ f := IsOpenImmersion.lift_fac _ _ _
    exact ⟨k, hk, fun l hl => (cancel_mono j).mp (hl.trans hk.symm)⟩
  · rintro ⟨k, hk, _⟩ z
    exact ⟨k z, congrArg (fun m : Z ⟶ Y => m z) hk⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProperMapImmersionLocus
