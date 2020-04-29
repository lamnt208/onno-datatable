import React from 'react'
import PropTypes from 'prop-types';
import styles from './styles.module.css';
import bootstrap from 'bootstrap/dist/css/bootstrap.css';

class Table extends React.Component {
	constructor(props) {
		super(props);
		this.state = {
			realData: [],
			dataRender: [],
			pageSize: 5,
			currentPage: 0,
			columns: [],
		}
	}

	componentWillMount() {
		const { data, children, api } = this.props;
		this.setState({ dataRender: data, realData: data, columns: children.map(child => child.props) });
	}

	getPageList(totalPages, page, maxLength) {
		if (maxLength < 5) throw "maxLength must be at least 5";

		const range = (start, end) => {
			return Array.from(Array(end - start + 1), (_, i) => i + start);
		}

		var sideWidth = maxLength < 9 ? 1 : 2;
		var leftWidth = (maxLength - sideWidth * 2 - 3) >> 1;
		var rightWidth = (maxLength - sideWidth * 2 - 2) >> 1;
		if (totalPages <= maxLength) {
			return range(1, totalPages);
		}
		if (page <= maxLength - sideWidth - 1 - rightWidth) {
			return range(1, maxLength - sideWidth - 1)
				.concat(0, range(totalPages - sideWidth + 1, totalPages));
		}
		if (page >= totalPages - sideWidth - 1 - rightWidth) {
			return range(1, sideWidth)
				.concat(0, range(totalPages - sideWidth - 1 - rightWidth - leftWidth, totalPages));
		}
		return range(1, sideWidth)
			.concat(0, range(page - leftWidth, page + rightWidth),
				0, range(totalPages - sideWidth + 1, totalPages));
	}

	onSort = (column, index) => () => {
		if (!column.sortable) {
			return false;
		}
		const { realData } = this.state;
		let dataRender = realData;
		let { sortingBy } = column;
		if (!sortingBy || sortingBy === 'DESC') {
			dataRender = realData.sort((a, b) => (a[column.field] > b[column.field]) ? 1 : -1);
			sortingBy = 'ASC';
		} else {
			dataRender = realData.sort((a, b) => (a[column.field] <= b[column.field]) ? 1 : -1);
			sortingBy = 'DESC';
		}
		const columns = this.state.columns.map(c => {
			return {
				...c,
				sortingBy: '',
			};
		});
		columns[index].sortingBy = sortingBy;
		this.setState({ dataRender, columns });
	}

	search = (e) => {
		const value = e.target.value;
		const fields = this.props.children.map(child => child.props).map(c => c.field);

		const dataRender = this.state.realData.filter(record => {
			for (let index = 0; index < fields.length; index++) {
				const field = fields[index];
				if (record[field] && `${record[field]}`.toLowerCase().includes(value.toLowerCase())) {
					return true;
				}
			}
			return false;
		});
		this.setState({ dataRender });
	}

	onChangePage = (page, disabled) => () => {
		if (disabled) {
			return;
		}
		this.setState({ currentPage: page });
	}

	onChangePageSize = (e) => {
		this.setState({ pageSize: +e.target.value });
	}

	renderPageSizeSelect() {
		const { pageSize } = this.state;
		const { pageSizes } = this.props;
		const className = `${bootstrap['custom-select']} ${bootstrap['custom-select-sm']} ${bootstrap['form-control']} ${bootstrap['form-control-sm']}`;
		let optionNode = [];
		for (let i = 0; i < pageSizes.length; i++) {
			optionNode.push(<option value={pageSizes[i]}>{pageSizes[i]}</option>);
		}
		return (
			<label className={styles.labelPageSize}>
				Show <select onChange={this.onChangePageSize} value={pageSize} className={className}>
					{optionNode}
				</select> entries
			</label>
		);
	}

	renderFilter() {
		const { filterable } = this.props;
		if (!filterable) {
			return null;
		}
		const className = `${bootstrap['form-control']} ${bootstrap['form-control-sm']}`;
		return <label className={styles.labelFilter}>
			Search: <input type="text" className={className} onChange={this.search} />
		</label>;
	}

	renderHeaderColumn(column, index) {
		const { sortIcon, sortAscIcon, sortDescIcon } = this.props;
		if (column.hidden) {
			return '';
		}
		let icon = sortIcon;
		if (column.sortingBy === 'ASC') {
			icon = sortAscIcon;
		} else if (column.sortingBy === 'DESC') {
			icon = sortDescIcon;
		}
		return (
			<th onClick={this.onSort(column, index)}>
				{column.label}
				{column.sortable ? icon : ''}
			</th>
		);
	}

	renderCell(record, column) {
		if (column.hidden) {
			return <></>;
		}
		if (column.render) {
			return <td>{column.render(record)}</td>;
		}
		if (column.field) {
			return <td>{record[column.field]}</td>
		}
		return <td></td>;
	}

	renderPagination() {
		const { dataRender, pageSize, currentPage } = this.state;

		const totalPage = Math.ceil(dataRender.length * 1.0 / pageSize);
		const pageList = this.getPageList(totalPage, currentPage, 8);
		let pageNode = [];
		for (let i = 0; i < pageList.length; i++) {
			pageNode.push(<li className={`${bootstrap['page-item']} ${pageList[i] - 1 === currentPage ? bootstrap.active : (pageList[i] === 0 ? bootstrap.disabled : '')}`}
				onClick={this.onChangePage(pageList[i] - 1, pageList[i] === 0)}>
				<a class={bootstrap['page-link']} href="javascript:void(0)">{pageList[i] === 0 ? '...' : pageList[i]}</a>
			</li>);
		}
		return (
			<nav className={styles.pagination} aria-label="...">
				<ul className={bootstrap.pagination}>
					<li className={`${bootstrap['page-item']} ${currentPage === 0 ? bootstrap.disabled : ''}`} onClick={this.onChangePage(currentPage - 1, currentPage === 0)}>
						<a className={bootstrap['page-link']} href="javascript:void(0)" tabindex="-1" aria-disabled="true">Previous</a>
					</li>
					{pageNode}
					<li className={`${bootstrap['page-item']} ${currentPage === totalPage - 1 ? bootstrap.disabled : ''}`} onClick={this.onChangePage(currentPage + 1, currentPage === totalPage - 1)}>
						<a className={bootstrap['page-link']} href="javascript:void(0)">Next</a>
					</li>
				</ul>
			</nav>
		);
	}

	render() {
		const { dataRender, pageSize, currentPage, columns } = this.state;
		const { className, width } = this.props;
		return (
			<div className={styles.onnoTable}>
				<div className={bootstrap.row}>
					<div className={`${bootstrap['col-sm-12']} ${bootstrap['col-md-6']}`}>
						{this.renderPageSizeSelect()}
					</div>
					<div className={`${bootstrap['col-sm-12']} ${bootstrap['col-md-6']}`}>
						{this.renderFilter()}
					</div>
				</div>
				<div className={bootstrap.row}>
					<div className={bootstrap['col-sm-12']}>
						<table className={`${bootstrap.table} ${bootstrap['table-bordered']} ${className}`} width={width}>
							<thead>
								<tr>
									{columns.map((column, index) => this.renderHeaderColumn(column, index))}
								</tr>
							</thead>
							<tbody>
								{dataRender.slice(currentPage * pageSize, currentPage * pageSize + pageSize).map(record => (
									<tr>
										{columns.map(column => this.renderCell(record, column))}
									</tr>
								))}
							</tbody>
						</table>
					</div>
				</div>
				<div className={bootstrap.row}>
					<div className={`${bootstrap['col-sm-12']} ${bootstrap['col-md-5']}`}>
						<label>Showing {(currentPage * pageSize) + 1} to {(currentPage * pageSize) + pageSize > dataRender.length ? dataRender.length : (currentPage * pageSize) + pageSize} of {dataRender.length} entries</label>
					</div>
					<div className={`${bootstrap['col-sm-12']} ${bootstrap['col-md-7']}`}>
						{this.renderPagination()}
					</div>
				</div>
			</div>
		);
	}
}

Table.propTypes = {
	children: PropTypes.element.isRequired,
	data: PropTypes.array.isRequired,
	width: PropTypes.string,
	className: PropTypes.string,
	pageSize: PropTypes.array,
	filterable: PropTypes.bool,
	sortAscIcon: PropTypes.node,
	sortDescIcon: PropTypes.node,
	sortIcon: PropTypes.node,
};

Table.defaultProps = {
	width: '100%',
	pageSizes: [5, 10, 25, 50, 75, 100],
	className: '',
	filterable: true,
	sortIcon: <i></i>,
	sortAscIcon: <i className={`${styles.arrow} ${styles.down}`}></i>,
	sortDescIcon: <i className={`${styles.arrow} ${styles.up}`}></i>,
};

export default Table;

class Column extends React.Component {
	constructor(props) {
		super(props);
	}

	render() {
		return ('');
	}
}

Column.propTypes = {
	label: PropTypes.string,
	field: PropTypes.string,
	sortable: PropTypes.bool,
	hidden: PropTypes.bool,
	render: PropTypes.func,
	sortingBy: PropTypes.string,
};

Column.defaultProps = {
	sortable: false,
	hidden: false,
	sortingBy: '',
};

export { Column };
