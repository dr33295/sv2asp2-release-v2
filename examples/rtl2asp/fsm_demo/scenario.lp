#const k = 5.
time(clk, 0..k).
val(state, idle, 0).
val(rst, 0, T) :- time(clk,T).
val(go, 1, 0).  val(go, 0, T) :- time(clk,T), T>=1.
val(done, 0, T) :- time(clk,T), T<3.
val(done, 1, T) :- time(clk,T), T>=3.
st(T,S) :- val(state, S, T).
#show st/2.
