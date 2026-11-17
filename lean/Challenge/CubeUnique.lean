import Challenge.Cube
namespace Packing.Cube
noncomputable def cubeSymm (v : Fin 3 → Bool) (σ : Equiv.Perm (Fin 3)) (x : Pt) : Pt :=
  WithLp.toLp 2 fun c => if v c then 1 - x (σ c) else x (σ c)

def IsUniqueUpToCubeSymm (N : ℕ) (d : ℝ) (q : Fin N → Pt) : Prop :=
  ∀ p : Fin N → Pt, (∀ i, InCube (p i)) → (∀ i j, i ≠ j → d ≤ dist (p i) (p j)) →
    ∃ (v : Fin 3 → Bool) (σ : Equiv.Perm (Fin 3)) (e : Equiv.Perm (Fin N)),
      ∀ i, p i = cubeSymm v σ (q (e i))

/-- Every arrangement of `N` points of the unit cube with pairwise distances at least `d` is
the image of `q`, in some order, under an isometry of space. -/
def IsUniqueUpToIsometry (N : ℕ) (d : ℝ) (q : Fin N → Pt) : Prop :=
  ∀ p : Fin N → Pt, (∀ i, InCube (p i)) → (∀ i j, i ≠ j → d ≤ dist (p i) (p j)) →
    ∃ (f : Pt → Pt) (e : Equiv.Perm (Fin N)), Isometry f ∧ ∀ i, p i = f (q (e i))

def IsUniqueMaxMinDist (N : ℕ) (d : ℝ) (q : Fin N → Pt) : Prop :=
  (∀ i, InCube (q i)) ∧ (∀ i j, i ≠ j → d ≤ dist (q i) (q j)) ∧
    (∀ p : Fin N → Pt, (∀ i, InCube (p i)) → ∃ i j, i ≠ j ∧ dist (p i) (p j) ≤ d) ∧
    IsUniqueUpToCubeSymm N d q

noncomputable def oppositeCorners : Fin 2 → Pt := fun i => corner fun _ => decide (i = 1)

/-- The definitions are not vacuous: at `d = 0` two points of the cube can coincide, and then
they are not an image of two opposite corners. -/
theorem isUniqueMaxMinDist_two : IsUniqueMaxMinDist 2 (Real.sqrt 3) oppositeCorners := by
  sorry

end Packing.Cube
