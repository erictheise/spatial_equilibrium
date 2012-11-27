{$R-}    {Range checking off}
{$I+}    {I/O checking on}
{$N-}    {No numeric coprocessor}

program SINGLE_COMMODITY_EXPANDING_EQUILBIRIUM_ALGORITHM;

{Copyright 1987 Eric S. Theise.  All rights reserved.}


Uses
  Crt,Dos;

const
  region_max = 100;
  msg = '  (Y) continues detailed output, any other key gives final solution';
  hd='    Node   Pred  TS   NOS     Flow     Intercept     Slope       Price';

type
  name = string[10];
  longname = string[14];
  longword = string[50];

  input_data = record
               node_id: byte;
               intercept: real;
               slope: real;
               end;

  ptr = ^node_data;
  node_data = record
              node_id: byte;
              intercept: real;
              slope: real;
              price: real;
              excess: real;
              trade_status: -1..1;
              pred: ptr;
              nos: byte;  {number of successors label, includes self}
              sos: real;  {slopes of successors label, includes self}
              flow: real;
              thread: ptr;
              end;

var
  choice,sort: char;
  skip: Boolean;
  i,j,k,n: byte;
  top,root,last_root,current,holder,left,right,
    d2_pointer,in_tree,out_tree: ptr;
  delta,max_excess: real;
  input_record: input_data;
  order: array [0..region_max] of ptr;
  demandfile: file of input_data;
  costfile: file of real;
  filename: name;
  dev: text;
  iteration_node,iteration_counter: array [1..region_max] of byte;
  cost: array [1..region_max,1..region_max] of real;
  start_time,sort_time,run_time,total_time: real;


function EXISTS(checkname: longname): Boolean;
  var
    fil: file;
  begin
  assign(fil,checkname);
  {$I-}
  reset(fil);
  {$I+}
  EXISTS := (IOresult = 0);
  end;



function TIME: real;
  type
    regpack = registers;
  var
    recpack: regpack;
  begin
  recpack.ax := $2c00;
  intr($21,Dos.Registers(recpack));
  with recpack do
    TIME := 3600.0 * (cx shr 8) + 60.0 * (cx mod 256)
            + (dx shr 8) + 0.01 * (dx mod 256);
  end;



procedure LOAD_DATA;
  var
    i,j: byte;
  begin
  reset(demandfile);
  reset(costfile);
  n := filesize(demandfile);
  for i := 1 to n do
    for j := 1 to n do
      read(costfile,cost[i,j]);
  close(costfile);

  new(top);
  top^.slope := 1E6;
  current := top;
  order[0] := top;

  for i := 1 to n do
    begin
    read(demandfile,input_record);
    new(root);
    with root^ do
      begin
      node_id := input_record.node_id;
      intercept := input_record.intercept;
      slope := input_record.slope;
      price := intercept/slope;
      excess := 0.0;
      trade_status := 0;
      pred := nil;
      nos := 1;
      sos := slope;
      flow := 0.0;
      thread := nil;
      end;
    current := root;
    order[i] := root;
    end;

  close(demandfile);
  end;      {of procedure LOAD_DATA}



procedure INSERTION_SORT;
  var
    i,j: byte;
    t: real;
    u: ptr;
  begin
  for i := 1 to n do
    begin
    j := i;
    t := order[i]^.slope;
    u := order[i];
    while t > order[j-1]^.slope do
      begin
      order[j] := order[j-1];
      j := j-1;
      end;
    order[j] := u;
    end;
  end;     {of procedure INSERTION_SORT}


procedure MARKET_CLEAR;
begin
holder := root;
current := root;
repeat
  with current^ do
    excess := intercept - slope * price;
  current := current^.thread;
  for i := 1 to holder^.nos - 1 do
    begin
    with current^ do
      begin
      excess := intercept - slope * price - flow;
      pred^.excess := pred^.excess + flow;
      end;
    current := current^.thread;
    end;
  holder := current;
until current = root;

max_excess := 0.0;
repeat
  if abs(current^.excess) > max_excess
    then max_excess := abs(current^.excess);
  current := current^.thread;
until current = root;
end;


procedure FOREST_STATUS(from_where: longword);
  begin
  writeln(dev,'  Forest status ',from_where,':');
  current := root;
  holder := root;
  writeln(dev,hd);
  repeat
    with current^ do
      begin
      write(dev,'     ',node_id:3,'    ');
      if pred <> nil
        then write(dev,pred^.node_id:3)
        else write(dev,'nil');
      writeln(dev,'  ',trade_status:2,'  ',nos:3,'  ',flow:10:5,'  ',
              intercept:10:5,'  ',slope:10:5,'  ',price:10:5);
      end;
    current := current^.thread;
  until current = holder;
  end;


procedure FOREST_UPDATE(attach_to,attacher: ptr);
  var
    i: byte;
    path_leader,path_mid,path_follower: ptr;
  begin
  path_follower := attacher;
  path_mid := attacher;
  path_leader := path_mid^.pred;
  right := attacher; left := nil; holder := nil;
  for i := 1 to path_mid^.nos - 1 do
    right := right^.thread;
  while path_leader <> nil do
    begin
    left := path_leader;
    while left^.thread <> path_mid do
      begin
      left := left^.thread;
      with path_leader^ do
        begin
        nos := nos - left^.nos;
        sos := sos - left^.sos;
        end;
      current := left;
      for i := 1 to current^.nos - 1 do
        left := left^.thread;
      end;
    holder := right^.thread;
    right^.thread := path_leader;
    left^.thread := holder;
    path_follower := path_mid;
    path_mid := path_leader;
    path_leader := path_mid^.pred;
    with path_mid^ do
      begin
      pred := path_follower;
      nos := attach_to^.nos - nos;
      sos := attach_to^.sos - attach_to^.slope - (sos - slope);
      end;
    right := left;
    while right^.thread^.pred = path_mid do
      begin
      right := right^.thread;
      with path_mid^ do
        begin
        nos := nos + right^.nos;
        sos := sos + right^.sos;
        end;
      current := right;
      for i := 1 to current^.nos - 1 do
        right := right^.thread;
      end;
    end;

  current := last_root;
  if attacher <> last_root then
    while current <> attacher do
      begin
      current^.flow := - current^.pred^.flow;
      current := current^.pred;
      end;

  with attacher^ do
    begin
    pred := attach_to;
    trade_status := -attach_to^.trade_status;
    nos := attach_to^.nos - 1;
    sos := attach_to^.sos - attach_to^.slope;
    flow := 0.0;
    end;

  end;     {of procedure FOREST_UPDATE}


procedure SPLICE;
  var
    i: byte;
    nos_holder: byte;
    sos_holder: real;
    marker_1,marker_2: ptr;
  begin
  current := in_tree;
  for i := 1 to in_tree^.nos - 1 do
    current := current^.thread;
  marker_1 := current^.thread;
  last_root := out_tree;
  while last_root^.pred <> nil do
    last_root := last_root^.pred;
  marker_2 := in_tree;
  while marker_2^.thread <> last_root do
    marker_2 := marker_2^.thread;
  current^.thread := out_tree;
  with in_tree^ do
    begin
    nos_holder := nos - 1;
    sos_holder := sos - slope;
    nos := last_root^.nos + 1;
    sos := last_root^.sos + slope;
    end;
  FOREST_UPDATE(in_tree,out_tree);
  if marker_1 <> last_root
    then
      begin
      holder := right^.thread;
      right^.thread := marker_1;
      marker_2^.thread := holder;
      end;
  with in_tree^ do
    begin
    nos := nos + nos_holder;
    sos := sos + sos_holder;
    end;
  current := in_tree^.pred;
  while current <> nil do
    begin
    with current^ do
      begin
      nos := nos + out_tree^.nos;
      sos := sos + out_tree^.sos;
      end;
    current := current^.pred;
    end;
  end;     {of procedure SPLICE}


procedure SPLIT;
  var
    i: byte;
  begin
  right := d2_pointer;
  left := d2_pointer^.pred;
  current := left;
  while left^.thread <> d2_pointer do
    left := left^.thread;
  with current^ do
    begin
    nos := nos - d2_pointer^.nos;
    sos := sos - d2_pointer^.sos;
    end;
  with d2_pointer^ do
    begin
    flow := 0.0;
    if nos = 1
      then trade_status := 0;
    pred := nil;
    for i := 1 to nos - 1 do
      right := right^.thread;
    end;
  left^.thread := right^.thread;
  while left^.thread^.pred <> nil do
    left := left^.thread;
  holder := left^.thread;
  left^.thread := d2_pointer;
  right^.thread := holder;
  current := current^.pred;
  while current <> nil do
    begin
    with current^ do
      begin
      nos := nos - d2_pointer^.nos;
      sos := sos - d2_pointer^.sos;
      end;
    current := current^.pred;
    end;
  end;     {of procedure SPLIT}


procedure PRICE_AND_FLOW_UPDATE(marker: ptr);
  begin
  repeat
    left := left^.thread;
    with left^ do
      begin
      price := price + delta;
      excess := intercept - slope * price;
      end;
  until left^.nos = 1;
  with left^ do
    begin
    flow := excess;
    pred^.excess := pred^.excess + flow;
    excess := 0.0;
    end;
  if left^.thread^.pred = left^.pred
    then PRICE_AND_FLOW_UPDATE(left)
    else right := left;

  while (left <> marker^.pred) and (left <> nil) do
    begin
    left := left^.pred;
    if left = right^.thread^.pred
      then
        begin
        left := right;
        PRICE_AND_FLOW_UPDATE(right^.thread^.pred^.thread);
        end
      else
        if left <> root then
          with left^ do
            begin
            flow := excess;
            pred^.excess := pred^.excess + flow;
            excess := 0.0;
            end;
    end;
  end;     {of procedure PRICE_AND_FLOW_UPDATE}


procedure RATIO;
  var
    i,left_node_id: byte;
    d1,d2,d2_temp,d3,dif_temp,dif: real;
    in_tree_temp,out_tree_temp: ptr;
  begin
  if root^.trade_status = -1
    then
      repeat
        iteration_counter[k] := iteration_counter[k] + 1;
        d1 := root^.excess/root^.sos;
        d2_pointer := nil; d2_temp := -1E6; d2 := -1E6;
        in_tree_temp := nil; in_tree := nil;
        out_tree_temp := nil; out_tree := nil;
        d3 := -1E6;

        current := root;
        while current^.thread^.pred <> nil do
          current := current^.thread;
        left := root;

        for i := 1 to root^.nos do
          begin
          if left^.trade_status = -1 then
            begin
            if i <> 1 then
              begin
              d2_temp := left^.flow/left^.sos;
              if d2_temp > d2 then
                begin
                d2 := d2_temp;
                d2_pointer := left;
                end;
              end;

            if current^.thread <> root then
              begin
              dif := -1E6; dif_temp := -1E6;
              left_node_id := left^.node_id;
              right := current^.thread;
              while right <> root do
                begin
                if right^.trade_status <> -1 then
                  begin
                  dif_temp := right^.price - cost[left_node_id,right^.node_id];
                  if dif_temp > dif then
                    begin
                    dif := dif_temp;
                    in_tree_temp := left;
                    out_tree_temp := right;
                    end;
                  end;
                right := right^.thread;
                end;
              dif := dif - left^.price;
              if dif > d3 then
                begin
                d3 := dif;
                in_tree := in_tree_temp;
                out_tree := out_tree_temp;
                end;
              end;
            end;
          left := left^.thread;
          end;

          if choice = 'Y' then
            begin
            run_time := run_time + TIME - start_time;
            writeln(dev,'  Results of Ratio test:');
            writeln(dev,'    d1 = ',d1:8:5);
            write(dev,'    d2 = ',d2:8:5);
            if d2_pointer <> nil
              then writeln(dev,' and is caused by node ',d2_pointer^.node_id)
              else writeln(dev);
            write(dev,'    d3 = ',d3:8:5);
            if in_tree <> nil
              then writeln(dev,' and is caused by arc ',in_tree^.node_id,',',
                                    out_tree^.node_id)
              else writeln(dev);
            writeln(dev);
            if not skip then
              begin
              writeln(msg); writeln;
              choice := upcase(ReadKey);
              end;
            start_time := TIME;
            end;

          if (d2 >= d1) and (d2 >= d3)
            then
              begin
              delta := d2;
              with root^ do
                begin
                price := price + delta;
                excess := intercept - slope * price;
                end;
              left := root;
              right := nil;
              PRICE_AND_FLOW_UPDATE(left^.thread);
              SPLIT;
              if choice = 'Y' then
                begin
                run_time := run_time + TIME - start_time;
                FOREST_STATUS('after Price and Flow Update and Split');
                writeln(dev);
                if not skip then
                  begin
                  writeln(msg); writeln;
                  choice := upcase(ReadKey);
                  end;
                start_time := TIME;
                end;
              end
            else
              if (d3 >= d1) and (d3 >= d2)
                then
                  begin
                  delta := d3;
                  with root^ do
                    begin
                    price := price + delta;
                    excess := intercept - slope * price;
                    end;
                  left := root;
                  right := nil;
                  PRICE_AND_FLOW_UPDATE(left^.thread);
                  SPLICE;
                  if choice = 'Y' then
                    begin
                    run_time := run_time + TIME - start_time;
                    FOREST_STATUS('after Price and Flow Update and Splice');
                    writeln(dev);
                    if not skip then
                      begin
                      writeln(msg); writeln;
                      choice := upcase(ReadKey);
                      end;
                    start_time := TIME;
                    end;
                end;

      until (d1 >= d2) and (d1 >= d3)

    else
      repeat
        iteration_counter[k] := iteration_counter[k] + 1;
        d1 := root^.excess/root^.sos;
        d2_pointer := nil; d2_temp := 1E6; d2 := 1E6;
        in_tree := nil; out_tree := nil; d3 := 1E6;

        current := root;
        while current^.thread^.pred <> nil do
          current := current^.thread;
        left := root;

        for i := 1 to root^.nos do
          begin
          if left^.trade_status = 1 then
            begin
            if i <> 1 then
              begin
              d2_temp := left^.flow/left^.sos;
              if d2_temp < d2 then
                begin
                d2 := d2_temp;
                d2_pointer := left;
                end;
              end;

            if current^.thread <> root then
              begin
              dif := 1E6; dif_temp := 1E6;
              left_node_id := left^.node_id;
              right := current^.thread;
              while right <> root do
                begin
                if right^.trade_status <> 1 then
                  begin
                  dif_temp := right^.price + cost[right^.node_id,left_node_id];
                  if dif_temp < dif then
                    begin
                    dif := dif_temp;
                    in_tree_temp := left;
                    out_tree_temp := right;
                    end;
                  end;
                right := right^.thread;
                end;
              dif := dif - left^.price;
              if dif < d3 then
                begin
                d3 := dif;
                in_tree := in_tree_temp;
                out_tree := out_tree_temp;
                end;
              end;
            end;
          left := left^.thread;
          end;

          if choice = 'Y' then
            begin
            run_time := run_time + TIME - start_time;
            writeln(dev,'  Results of Ratio test:');
            writeln(dev,'    d1 = ',d1:8:5);
            write(dev,'    d2 = ',d2:8:5);
            if d2_pointer <> nil
              then writeln(dev,' and is caused by node ',d2_pointer^.node_id)
              else writeln(dev);
            write(dev,'    d3 = ',d3:8:5);
            if in_tree <> nil
              then writeln(dev,' and is caused by arc ',in_tree^.node_id,',',
                           out_tree^.node_id)
              else writeln(dev);
            writeln(dev);
            if not skip then
              begin
              writeln(msg); writeln;
              choice := upcase(ReadKey);
              end;
            start_time := TIME;
            end;

          if (d2 <= d1) and (d2 <= d3)
            then
              begin
              delta := d2;
              with root^ do
                begin
                price := price + delta;
                excess := intercept - slope * price;
                end;
              left := root;
              right := nil;
              PRICE_AND_FLOW_UPDATE(left^.thread);
              SPLIT;
              if choice = 'Y' then
                begin
                run_time := run_time + TIME - start_time;
                FOREST_STATUS('after Price and Flow Update and Split');
                writeln(dev);
                if not skip then
                  begin
                  writeln(msg); writeln;
                  choice := upcase(ReadKey);
                  end;
                start_time := TIME;
                end;
              end
            else
              if (d3 <= d1) and (d3 <= d2)
                then
                  begin
                  delta := d3;
                  with root^ do
                    begin
                    price := price + delta;
                    excess := intercept - slope * price;
                    end;
                  left := root;
                  right := nil;
                  PRICE_AND_FLOW_UPDATE(left^.thread);
                  SPLICE;
                  if choice = 'Y' then
                    begin
                    run_time := run_time + TIME - start_time;
                    FOREST_STATUS('after Price and Flow Update and Splice');
                    writeln(dev);
                    if not skip then
                      begin
                      writeln(msg); writeln;
                      choice := upcase(ReadKey);
                      end;
                    start_time := TIME;
                    end;
                end;

    until (d1 <= d2) and (d1 <= d3);

  delta := d1;
  with root^ do
    begin
    price := price + delta;
    excess := intercept - slope * price;
    end;
  left := root;
  right := nil;
  PRICE_AND_FLOW_UPDATE(left^.thread);
  if choice = 'Y' then
    begin
    run_time := run_time + TIME - start_time;
    FOREST_STATUS('after Price and Flow Update');
    writeln(dev);
    if not skip then
      begin
      writeln(msg); writeln;
      choice := upcase(ReadKey);
      end;
    start_time := TIME;
    end;
  end;     {of procedure RATIO}


procedure MAIN_LOOP;
  var
    L,U,L_temp,U_temp: real;
    export_to,import_from: ptr;
  begin

  root := order[1];
  root^.thread := root;
  iteration_node[1] := root^.node_id;
  iteration_counter[1] := 0;

  for k := 2 to n do
    begin
    start_time := TIME;
    current := root;
    root := order[k];
    iteration_node[k] := root^.node_id;
    iteration_counter[k] := 0;
    export_to := nil;
    import_from := nil;
    L := -1E6; U :=  1E6;
    holder := current;
    repeat
      if current^.trade_status <> 1 then
        begin
        U_temp := current^.price + cost[current^.node_id,root^.node_id];
        if U_temp < U then
          begin
          U := U_temp;
          import_from := current;
          end;
        end;
      if current^.trade_status <> -1 then
        begin
        L_temp := current^.price - cost[root^.node_id,current^.node_id];
        if L_temp > L then
          begin
          L := L_temp;
          export_to := current;
          end;
        end;
      current := current^.thread
    until current = holder;

    if root^.price > U
      then
        begin
        if choice = 'Y' then
          begin
          run_time := run_time + TIME - start_time;
          writeln(dev); writeln(dev);
          writeln(dev,'Bringing node ',root^.node_id,' into equilibrium ...');
          writeln(dev);
          writeln(dev,'  L = ',L:4:2,', isolated price = ',root^.price:4:2,
                      ', U = ',U:4:2,': node ',root^.node_id,
                      ' imports from node ',import_from^.node_id);
          writeln(dev);
          if not skip then
            begin
            writeln(msg); writeln;
            choice := upcase(ReadKey);
            end;
          start_time := TIME;
          end;
        import_from^.trade_status := -1;
        last_root := import_from;
        while last_root^.pred <> nil do
          last_root := last_root^.pred;
        with root^ do
          begin
          price := U;
          excess := intercept - slope * price;
          trade_status := 1;
          nos := last_root^.nos + 1;
          sos := last_root^.sos + slope;
          thread := import_from;
          end;
        FOREST_UPDATE(root,import_from);
        if right^.thread <> root
          then
            begin
            while right^.thread <> last_root do
              right := right^.thread;
            right^.thread := root;
            end;
        if choice = 'Y' then
          begin
          run_time := run_time + TIME - start_time;
          FOREST_STATUS('after Main Loop'); writeln(dev);
          if not skip then
            begin
            writeln(msg); writeln;
            choice := upcase(ReadKey);
            end;
          start_time := TIME;
          end;
        RATIO;
        end
      else
        if root^.price < L
          then
            begin
            if choice = 'Y' then
              begin
              run_time := run_time + TIME - start_time;
              writeln(dev); writeln(dev);
              writeln(dev,'Bringing node ',root^.node_id,' into equilibrium ...');
              writeln(dev);
              writeln(dev,'  L = ',L:4:2,', isolated price = ',root^.price:4:2,
                          ', U = ',U:4:2,': node ',root^.node_id,
                          ' exports to node ',export_to^.node_id);
              writeln(dev);
              if not skip then
                begin
                writeln(msg); writeln;
                choice := upcase(ReadKey);
                end;
              start_time := TIME;
              end;
            export_to^.trade_status := 1;
            last_root := export_to;
            while last_root^.pred <> nil do
              last_root := last_root^.pred;
            with root^ do
              begin
              price := L;
              excess := intercept - slope * price;
              trade_status := -1;
              nos := last_root^.nos + 1;
              sos := last_root^.sos + slope;
              thread := export_to;
              end;
            FOREST_UPDATE(root,export_to);
            if right^.thread <> root
              then
                begin
                while right^.thread <> last_root do
                  right := right^.thread;
                right^.thread := root;
                end;
            if choice = 'Y' then
              begin
              run_time := run_time + TIME - start_time;
              FOREST_STATUS('after Main Loop'); writeln(dev);
              if not skip then
                begin
                writeln(msg); writeln;
                choice := upcase(ReadKey);
                end;
              start_time := TIME;
              end;
            RATIO;
            end
          else
            begin
            if choice = 'Y' then
              begin
              run_time := run_time + TIME - start_time;
              writeln(dev); writeln(dev);
              writeln(dev,'Bringing node ',root^.node_id,' into equilibrium ...');
              writeln(dev);
              writeln(dev,'  L = ',L:4:2,', isolated price = ',root^.price:4:2,
                          ', U = ',U:4:2,': node ',root^.node_id,
                          ' is isolated');
              writeln(dev);
              if not skip then
                begin
                writeln(msg); writeln;
                choice := upcase(ReadKey);
                end;
              start_time := TIME;
              end;
            root^.trade_status := 0;
            root^.thread := current;
            repeat
              current := current^.thread;
            until current^.thread = holder;
            current^.thread := root;
            end;

    run_time := run_time + TIME - start_time;

    end;
  end;    {of procedure MAIN_LOOP}


begin
clrscr;
write('The expanding equilibrium algorithm for ');
writeln('linear single commodity problems');
writeln('Copyright 1987 Eric S. Theise.  All rights reserved.');
writeln;
repeat
  skip := true;
  write('What is the name of the problem to be solved? (ctrl-Break to quit)  ');
  readln(filename); writeln;
  if not EXISTS(filename + '.DEM') then
    begin
    writeln('  ',filename + '.DEM',' is not on this disk'); writeln;
    skip := false;
    end;
  if not EXISTS(filename + '.Cij') then
    begin
    writeln('  ',filename + '.Cij',' is not on this disk'); writeln;
    skip := false;
    end;
until skip;

writeln('Where should output be sent:');
writeln('     Screen  (S)?');
writeln('     Printer (P)?');
writeln('     or File (F)?');
choice := upcase(ReadKey); writeln;
case choice of
  'P': begin
       assign(dev,'LPT1');
       skip := true;
       end;
  'F': begin
       assign(dev,filename+'.OUT');
       writeln('Output will be sent to file ',filename+'.OUT'); writeln;
       skip := true;
       end;
  else begin
       assigncrt(dev);
       skip := false;
       end;
  end;
rewrite(dev);
write('Do you want detailed output for each iteration? (Y/N) ');
choice := upcase(ReadKey); writeln(choice); writeln;
write('Do you want regions sorted by excess demand function slopes? (Y/N) ');
sort := upcase(ReadKey); writeln(sort);
writeln; writeln('Working ...'); writeln;
assign(demandfile,filename + '.DEM');
assign(costfile,filename + '.Cij');
LOAD_DATA;
if sort <> 'N'
  then
    begin
    sort_time := TIME;
    INSERTION_SORT;
    sort_time := TIME - sort_time;
    end
  else sort_time := 0.0;
run_time := 0.0;
MAIN_LOOP;
if skip then
  begin
  writeln(dev,'The expanding equilibrium algorithm on ',filename);
  writeln(dev);
  end;
FOREST_STATUS('at final solution'); writeln(dev);
if not skip then
  begin
  writeln('Any key to continue ...'); choice := ReadKey; writeln;
  end;
for j := 1 to n do
  writeln(dev,'Bringing node ',iteration_node[j]:3,' into equilibrium required ',
                  iteration_counter[j]:2,' Ratio tests');
writeln(dev);
write(dev,'Insertion sort time:        ');
if sort <> 'N'
  then writeln(dev,sort_time:10:2,' seconds')
  else writeln(dev,'sort not performed');
writeln(dev,'Expanding equilibrium time:  ',run_time:9:2,' seconds');
total_time := sort_time + run_time;
writeln(dev,'Total CPU time:              ',total_time:9:2,' seconds');
writeln(dev);
MARKET_CLEAR;
writeln(dev,'Largest error: ',max_excess);
writeln(dev);
close(dev);
end.
