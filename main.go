package main

import (
	"fmt"

	"github.com/mitchellh/go-z3"
)

func main() {
	players := 16
	groups := 20
	// players := 9
	// groups := 12

	config := z3.NewConfig()
	ctx := z3.NewContext(config)
	config.Close()
	defer ctx.Close()

	// Create the solver
	s := ctx.NewSolver()
	defer s.Close()

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

	if works == z3.True {
		fmt.Println("works")
	} else {
		fmt.Println("doesn'twork", works)
	}

	m := s.Model()
	assignments := m.Assignments()
	m.Close()

	//		fmt.Println(ans)
	unwrapped := unwrap(state, assignments)

	for _, x := range unwrapped {
		for _, y := range x {
			fmt.Printf(" %2d ", y)
		}
		fmt.Print("\n")
	}

	groots := map[int][][2]int{}
	for i := 0; i < players; i++ {
		for j := 0; j < players; j++ {
			if i == j {
				continue
			}

			x := unwrapped[i][j]
			toast := groots[x]
			groots[x] = append(toast, [2]int{i, j})
		}
	}
	for grow, asdf := range groots {
		fmt.Println(grow, asdf)
	}
	for _, x := range prettify(groots) {
		fmt.Println(x)
	}
}

func prettify(x map[int][][2]int) [][]int {
	ans := make([][]int, len(x))
	for k, v := range x {

		tmp := map[int]bool{}

		for _, ij := range v {
			tmp[ij[0]] = true
			tmp[ij[1]] = true
		}

		ans[k] = []int{}
		for z := range tmp {

			ans[k] = append(ans[k], z)

		}

	}
	return ans

}

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
	ans := make([][]int, len(state))
	for i := 0; i < len(state); i++ {
		ans[i] = make([]int, len(state))
		for j := 0; j < len(state); j++ {
			ans[i][j] = -1
		}
	}

	for i := 0; i < len(state); i++ {
		for j := 0; j < len(state[i]); j++ {
			for k := 0; k < len(state[i][j]); k++ {
				if ants, ok := solved[state[i][j][k].String()]; ok && ants.String() == "true" {
					if ans[i][j] != -1 {
						panic("")
					}
					ans[i][j] = k
				}
			}
		}
	}
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
