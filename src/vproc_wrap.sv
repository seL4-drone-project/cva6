
module vproc_wrap import ariane_pkg::*; (
        input  logic                     clk_i,
        input  logic                     rst_ni,

        output logic                     vect_ready_o,
        input  logic                     instr_valid_i,
        input  logic [TRANS_ID_BITS-1:0] trans_id_i,
        input  logic [31:0]              instr_i,
        input  logic [riscv::XLEN-1:0]   x_rs1_i,
        input  logic [riscv::XLEN-1:0]   x_rs2_i,
        output logic                     vect_valid_o,
        output logic [TRANS_ID_BITS-1:0] vect_trans_id_o,
        output logic [riscv::XLEN-1:0]   vect_result_o
    );

    logic                     instr_valid_q, instr_valid_d;
    logic [TRANS_ID_BITS-1:0] trans_id_q,    trans_id_d;
    logic [31:0]              instr_q,       instr_d;
    logic [31:0]              x_rs1_q,       x_rs1_d;
    logic [31:0]              x_rs2_q,       x_rs2_d;
    logic                     rd_wait_q,     rd_wait_d;

    always_ff @(posedge clk_i or negedge rst_ni) begin : vproc_wrap_buf
        if (~rst_ni) begin
            instr_valid_q <= '0;
            trans_id_q    <= '0;
            instr_q       <= '0;
            x_rs1_q       <= '0;
            x_rs2_q       <= '0;
            rd_wait_q     <= '0;
        end else begin
            instr_valid_q <= instr_valid_d;
            trans_id_q    <= trans_id_d;
            instr_q       <= instr_d;
            x_rs1_q       <= x_rs1_d;
            x_rs2_q       <= x_rs2_d;
            rd_wait_q     <= rd_wait_d;
        end
    end

    logic        instr_gnt;
    logic        instr_illegal;
    logic        rd_wait;
    logic        rd_valid;
    logic [31:0] rd;

    vproc_core #(
        //.VREG_SZ          (                 ),
        //.VMEM_SZ          (                 ),
        //.MUL_OP_SZ        (                 ),
        //.ALU_OP_SZ        (                 ),
        //.SLD_OP_SZ        (                 )
    ) v_core (
        .clk_i            ( clk_i           ),
        .rst_ni           ( rst_ni          ),
        .instr_valid_i    ( instr_valid_q   ),
        .instr_i          ( instr_q         ),
        .x_rs1_i          ( x_rs1_q         ),
        .x_rs2_i          ( x_rs2_q         ),
        .instr_gnt_o      ( instr_gnt       ),
        .instr_illegal_o  ( instr_illegal   ),
        .misaligned_ls_o  (                 ),
        .rd_wait_o        ( rd_wait         ),
        .rd_valid_o       ( rd_valid        ),
        .rd_o             ( rd              ),
        .csr_vtype_o      (                 ),
        .csr_vl_o         (                 ),
        .csr_vlenb_o      (                 ),
        .csr_vstart_o     (                 ),
        .csr_vstart_i     ( '0              ),
        .csr_vstart_set_i ( '0              ),
        .csr_vcsr_o       (                 ),
        .csr_vcsr_i       ( '0              ),
        .csr_vcsr_set_i   ( '0              ),
        .data_req_o       (                 ),
        .data_gnt_i       ( '0              ),
        .data_rvalid_i    ( '0              ),
        .data_err_i       ( '0              ),
        .data_rdata_i     ( '0              ),
        .data_addr_o      (                 ),
        .data_we_o        (                 ),
        .data_be_o        (                 ),
        .data_wdata_o     (                 )
    );

    always_comb begin
        instr_valid_d = instr_valid_q;
        trans_id_d    = trans_id_q;
        instr_d       = instr_q;
        x_rs1_d       = x_rs1_q;
        x_rs2_d       = x_rs2_q;
        rd_wait_d     = rd_wait_q;

        if (vect_ready_o & instr_valid_i) begin
            instr_valid_d = 1'b1;
            trans_id_d    = trans_id_i;
            instr_d       = instr_i;
            x_rs1_d       = x_rs1_i[31:0];
            x_rs2_d       = x_rs2_i[31:0];
        end
        if (instr_valid_q & instr_gnt) begin
            instr_valid_d = 1'b0;
        end

        if (instr_valid_q & instr_gnt & rd_wait) begin
            rd_wait_d = 1'b1;
        end
        if (rd_wait_q & rd_valid) begin
            rd_wait_d = 1'b0;
        end
    end

    logic instr_ack_no_wait;
    assign instr_ack_no_wait = instr_valid_q & instr_gnt & ~rd_wait;

    assign vect_ready_o    = (~rd_wait_q | rd_valid) & (~instr_valid_q | instr_ack_no_wait);
    assign vect_valid_o    = ( rd_wait_q & rd_valid) | instr_ack_no_wait;
    assign vect_trans_id_o = trans_id_q;
    assign vect_result_o   = rd;

endmodule
