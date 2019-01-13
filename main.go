package main

import (
	"fmt"
	"sort"

	"github.com/mitchellh/go-z3"
)

func main() {
	players := 16
	groups := 20
	// players := 9
	// groups := 12

	ans, err := solve(players, groups)
	if err == nil {
		for i := 0; i < groups; i++ {
			fmt.Println(ans[i])
		}

	} else {
		fmt.Println("no solution for", players, groups)
	}

}

func solve(players, groups int) ([][]int, error) {

	config := z3.NewConfig()
	ctx := z3.NewContext(config)
	config.Close()
	defer ctx.Close()

	s := ctx.NewSolver()
	defer s.Close()

	// A "true" in position i,j,g means that players i and j play one another as
	// part of subgroup g
	state := VarTensor(ctx, players, players, groups)

	// Each possible combination of games must be played in exactly one group
	for i := 0; i < players; i++ {
		for j := i + 1; j < players; j++ {
			s.Assert(Unique(state[i][j]...))
		}
	}

	// symmetric property
	for i := 0; i < players; i++ {
		for j := i + 1; j < players; j++ {
			for u := 0; u < groups; u++ {
				s.Assert(
					state[i][j][u].Eq(state[j][i][u]),
				)
			}
		}
	}

	for u := 0; u < groups; u++ {
		all := []*z3.AST{}

		for i := 0; i < players; i++ {
			for j := i + 1; j < players; j++ {
				all = append(all, state[i][j][u])
			}
		}

		// No group can have only one game
		s.Assert(Unique(all...).Not())

		// No group can have no players
		s.Assert(all[0].Or(all[1:]...))
	}

	// If players i and j play one another in group g and so do j and k, then i
	// and k must play one another in group g.
	for i := 0; i < players; i++ {
		for j := i + 1; j < players; j++ {
			for a := j + 1; a < players; a++ {
				for x := 0; x < groups; x++ {
					s.Assert(state[i][j][x].And(state[a][j][x]).Implies(state[a][i][x]))
					s.Assert(state[i][j][x].And(state[a][i][x]).Implies(state[a][j][x]))
					s.Assert(state[a][i][x].And(state[a][j][x]).Implies(state[i][j][x]))
				}
			}
		}
	}

	// If players i and j play one another in group g and so do k and l, then
	// i,k i,l j,k and j,l must all be played in group g.
	for i := 0; i < players; i++ {
		for j := i + 1; j < players; j++ {
			for a := j + 1; a < players; a++ {
				for b := a + 1; b < players; b++ {
					for x := 0; x < groups; x++ {
						s.Assert(
							state[i][j][x].And(state[a][b][x]).Implies(
								state[i][a][x].And(state[i][b][x], state[j][a][x], state[j][b][x])),
						)

						s.Assert(
							state[i][a][x].And(state[j][b][x]).Implies(
								state[i][j][x].And(state[i][b][x], state[j][a][x], state[a][b][x])),
						)

						s.Assert(
							state[i][b][x].And(state[j][a][x]).Implies(
								state[i][j][x].And(state[i][a][x], state[j][b][x], state[a][b][x])),
						)
					}
				}
			}
		}
	}

	works := s.Check()

	if works != z3.True {
		return [][]int{}, fmt.Errorf("no solution")
	}

	m := s.Model()
	assignments := m.Assignments()
	m.Close()

	return unwrap(state, assignments), nil
}

// Exactly one of the vars is true
func Unique(vars ...*z3.AST) *z3.AST {
	x := vars[0].Or(vars[1:]...)

	for i := 0; i < len(vars); i++ {
		for j := i + 1; j < len(vars); j++ {
			x = x.And(vars[i].Implies(vars[j].Not()))
		}
	}

	return x
}

func unwrap(state [][][]*z3.AST, solved map[string]*z3.AST) [][]int {
	numGroups := len(state[0][0])

	ans := make([][]int, numGroups)
	groups := map[int]map[int]bool{}
	for i := 0; i < numGroups; i++ {
		groups[i] = map[int]bool{}
		ans[i] = []int{}
	}

	for i := 0; i < len(state); i++ {
		for j := 0; j < len(state[i]); j++ {
			for k := 0; k < len(state[i][j]); k++ {
				seen := false

				if ants, ok := solved[state[i][j][k].String()]; ok && ants.String() == "true" {
					if seen {
						panic("should never happen")
					}
					seen = true
					groups[k][i] = true
					groups[k][j] = true
				}
			}
		}
	}

	for i, g := range groups {
		for x := range g {
			ans[i] = append(ans[i], x)
		}
		sort.Ints(ans[i])
	}

	sort.Slice(ans, func(i, j int) bool { return ans[i][0] < ans[j][0] })
	return ans
}

func VarTensor(ctx *z3.Context, a, b, c int) [][][]*z3.AST {
	stateMat := make([][][]*z3.AST, a)

	for i := 0; i < a; i++ {
		stateMat[i] = make([][]*z3.AST, b)

		for j := 0; j < b; j++ {

			stateMat[i][j] = make([]*z3.AST, c)

			for z := 0; z < c; z++ {
				name := fmt.Sprintf("v-%d-%d-%d", i, j, z)
				stateMat[i][j][z] = ctx.Const(
					ctx.Symbol(name),
					ctx.BoolSort(),
				)
			}
		}

	}
	return stateMat
}
